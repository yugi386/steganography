use aes_gcm::{
    Aes256Gcm, Nonce,
    aead::{Aead, AeadCore, KeyInit, OsRng},
};
use anyhow::{Context, Result, anyhow};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use clap::{Parser, Subcommand};
use image::{DynamicImage, GenericImageView, ImageBuffer, Rgba};
use rand::seq::SliceRandom; // Importante para o embaralhamento
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::fs::{self};
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};

// --- CLI CONFIGURATION ---
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    // Ocultar -> Hide
    Hide {
        #[arg(short, long)]
        input_dir: String,
        #[arg(short, long)]
        file: String,
        #[arg(short, long)]
        output_dir: String,
        #[arg(short, long)]
        password: String,
        #[arg(short, long, default_value_t = 2)]
        bits: u8,
    },
    // Recuperar -> Recover
    Recover {
        #[arg(short, long)]
        input_img: String, // ou start_img
        #[arg(short, long)]
        password: String,
    },
    // GerarIscas -> Decoys (ou GenerateDecoys)
    Decoys {
        #[arg(short, long)]
        input_dir: String,
        #[arg(short, long)]
        output_dir: String,
        #[arg(short, long, default_value_t = 2)]
        bits: u8,
    },
    // Scan já está em inglês
    Scan {
        #[arg(short, long)]
        dir: String,
        #[arg(short, long)]
        password: String,
    },
}

// --- DATA STRUCTURES ---

#[derive(Serialize, Deserialize, Debug)]
struct ChainHeader {
    chunk_len: u32,
    has_next: bool,
    next_filename: String,
    sequence_number: u32,
}

// --- AUXILIARY FUNCTIONS ---

fn derive_key(password: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(password.as_bytes());
    hasher.finalize().into()
}

fn compress_data(data: &[u8]) -> Result<Vec<u8>> {
    let mut output = Vec::new();
    lzma_rs::lzma_compress(&mut &data[..], &mut output)?;
    Ok(output)
}

fn decompress_data(data: &[u8]) -> Result<Vec<u8>> {
    let mut output = Vec::new();
    lzma_rs::lzma_decompress(&mut &data[..], &mut output)?;
    Ok(output)
}

fn encrypt_bytes(data: &[u8], key: &[u8; 32]) -> Result<Vec<u8>> {
    let cipher = Aes256Gcm::new(key.into());
    let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
    let ciphertext = cipher
        .encrypt(&nonce, data)
        .map_err(|e| anyhow!("AES Erro: {:?}", e))?;
    let mut res = nonce.to_vec();
    res.extend(ciphertext);
    Ok(res)
}

fn decrypt_bytes(data: &[u8], key: &[u8; 32]) -> Result<Vec<u8>> {
    if data.len() < 12 {
        return Err(anyhow!("Dados inválidos"));
    }
    let (nonce, cipher) = data.split_at(12);
    let aes = Aes256Gcm::new(key.into());
    let plaintext = aes
        .decrypt(Nonce::from_slice(nonce), cipher)
        .map_err(|_| anyhow!("Senha incorreta ou dados corrompidos"))?;
    Ok(plaintext)
}

// --- STEGANOGRAPHY LOGIC ---

fn calcular_capacidade_chunk(
    width: u32,
    height: u32,
    bits: u8,
    header_size_estimado: usize,
) -> usize {
    let total_pixels = (width * height) as usize;
    let total_bits = total_pixels * 3 * bits as usize;
    let total_bytes = total_bits / 8;

    let overhead = 4 + header_size_estimado;

    if total_bytes > overhead {
        total_bytes - overhead
    } else {
        0
    }
}

fn embed_raw_bits(
    img: &DynamicImage,
    data: &[u8],
    bits: u8,
) -> Result<ImageBuffer<Rgba<u8>, Vec<u8>>> {
    let (_w, _h) = img.dimensions();
    let mut out = img.to_rgba8();
    let total_bits = data.len() * 8;
    let mut cursor = 0;

    for pixel in out.pixels_mut() {
        for c in 0..3 {
            if cursor >= total_bits {
                break;
            }
            let mut val = pixel[c];
            let mask = !((1 << bits) - 1);
            val &= mask;

            let mut chunk = 0;
            for _ in 0..bits {
                if cursor < total_bits {
                    let byte = cursor / 8;
                    let bit_off = 7 - (cursor % 8);
                    let bit = (data[byte] >> bit_off) & 1;
                    chunk = (chunk << 1) | bit;
                    cursor += 1;
                } else {
                    chunk <<= 1;
                }
            }
            pixel[c] = val | chunk;
        }
        if cursor >= total_bits {
            break;
        }
    }
    Ok(out)
}

fn extract_raw_bits(
    img: &ImageBuffer<Rgba<u8>, Vec<u8>>,
    bits: u8,
    limit_bytes: Option<usize>,
    start_bit: usize,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut acc = 0u8;
    let mut acc_count = 0;
    let mut global_bit = 0;

    let stop_at_bit = limit_bytes.map(|l| start_bit + (l * 8));

    'outer: for pixel in img.pixels() {
        for c in 0..3 {
            if global_bit + (bits as usize) <= start_bit {
                global_bit += bits as usize;
                continue;
            }

            let val = pixel[c];
            let mask = (1 << bits) - 1;
            let val_bits = val & mask;

            for i in (0..bits).rev() {
                if global_bit < start_bit {
                    global_bit += 1;
                    continue;
                }

                if let Some(stop) = stop_at_bit {
                    if global_bit >= stop {
                        break 'outer;
                    }
                }

                let bit = (val_bits >> i) & 1;
                acc = (acc << 1) | bit;
                acc_count += 1;
                global_bit += 1;

                if acc_count == 8 {
                    bytes.push(acc);
                    acc = 0;
                    acc_count = 0;
                }
            }
        }
    }
    bytes
}

// --- MAIN FUNCTIONS ---

fn is_valid_image(ext: &OsStr) -> bool {
    let ext_str = ext.to_string_lossy().to_lowercase();
    matches!(
        ext_str.as_str(),
        "jpg" | "jpeg" | "png" | "bmp" | "webp" | "tif" | "tiff"
    )
}

use rand::Rng;

// use rand::seq::SliceRandom; // Importante para o .choose()

fn ocultar_em_lote(
    pasta_imgs: &str,
    arq_secreto: &str,
    pasta_saida: &str,
    senha: &str,
    bits: u8,
) -> Result<()> {
    println!("--- HIDE MODE (INFINITE RECYCLING) ---");

    // 1. Validate source
    if !Path::new(pasta_imgs).exists() {
        return Err(anyhow!("Source folder not found!"));
    }

    // Load all valid source images into memory (PathBufs)
    let imagens_originais: Vec<PathBuf> = fs::read_dir(pasta_imgs)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map_or(false, is_valid_image))
        .collect();

    if imagens_originais.is_empty() {
        return Err(anyhow!("No valid images in source folder."));
    }

    println!("Source pool size: {} images.", imagens_originais.len());

    // 2. Prepare Payload
    let raw_content = fs::read(arq_secreto).context("Read secret file")?;
    let filename_original = Path::new(arq_secreto)
        .file_name()
        .unwrap()
        .to_str()
        .unwrap();

    let mut package = Vec::new();
    package.write_u32::<BigEndian>(filename_original.len() as u32)?;
    package.extend_from_slice(filename_original.as_bytes());
    package.extend_from_slice(&raw_content);

    let compressed_stream = compress_data(&package)?;
    println!("Total payload size to hide: {} bytes", compressed_stream.len());

    // 3. Loop Setup
    let key = derive_key(senha);
    let mut cursor_stream = 0;
    let mut sequence_num = 0;
    let mut rng = rand::thread_rng();

    fs::create_dir_all(pasta_saida)?;

    // Generate the name for the FIRST file in the chain
    let mut current_out_name = generate_random_name(); 

    // 4. Processing Loop (While data remains)
    while cursor_stream < compressed_stream.len() {
        // --- KEY CHANGE: Pick ANY image from source pool randomly ---
        // This allows using 1 image to hide a 1GB file (it will be repeated)
        let img_in_path = imagens_originais.choose(&mut rng).unwrap();

        let img = image::open(img_in_path)
            .context("Error opening source img")?
            .to_rgba8();
        let (w, h) = img.dimensions();

        // Calculate Capacity
        let cap_bytes = calcular_capacidade_chunk(w, h, bits, 150);
        
        // Safety check against tiny images
        if cap_bytes == 0 {
            // In a robust system, we should remove this image from the list or warn.
            // For now, let's just pick another one in the next iteration.
            continue; 
        }

        let remaining = compressed_stream.len() - cursor_stream;
        let chunk_size = std::cmp::min(cap_bytes, remaining);
        let eh_ultimo = chunk_size == remaining;

        // Generate the name for the NEXT file (if needed)
        let next_out_name = if !eh_ultimo {
            generate_random_name() // Generate on the fly
        } else {
            String::new()
        };

        // Header Construction
        let header = ChainHeader {
            chunk_len: chunk_size as u32,
            has_next: !eh_ultimo,
            next_filename: next_out_name.clone(), // Point to the random name we just generated
            sequence_number: sequence_num,
        };

        // Encryption & Embedding (Same as before)
        let header_bytes = bincode::serialize(&header)?;
        let enc_header = encrypt_bytes(&header_bytes, &key)?;
        let chunk_data = &compressed_stream[cursor_stream..cursor_stream + chunk_size];
        let enc_chunk = encrypt_bytes(chunk_data, &key)?;

        let mut final_blob = Vec::new();
        final_blob.write_u32::<BigEndian>(enc_header.len() as u32)?;
        final_blob.extend(enc_header);
        final_blob.extend(enc_chunk);

        let img_dyn = DynamicImage::ImageRgba8(img);
        let stego_img = embed_raw_bits(&img_dyn, &final_blob, bits)?;

        // Save using current_out_name
        let out_path = Path::new(pasta_saida).join(&current_out_name);
        stego_img.save(&out_path)?;

        println!(
            "[{}] Saved '{}' (Seq: {}). Points to -> '{}'",
            sequence_num, current_out_name, sequence_num, 
            if eh_ultimo { "END" } else { &next_out_name }
        );

        // Update state for next iteration
        cursor_stream += chunk_size;
        sequence_num += 1;
        current_out_name = next_out_name; // The next file becomes the current one
    }

    println!("\nSUCCESS! Chain created with {} fragments.", sequence_num);

    // Apply security measures
    scramble_creation_order(pasta_saida)?;
    sanitizar_metadados(pasta_saida)?;

    Ok(())
}

// Helper function to keep code clean
fn generate_random_name() -> String {
    use rand::distributions::Alphanumeric;
    use rand::Rng;
    let s: String = rand::thread_rng()
        .sample_iter(&Alphanumeric)
        .take(8)
        .map(char::from)
        .collect();
    format!("{}.png", s)
}

fn recuperar_cadeia(primeira_imagem: &str, senha: &str) -> Result<()> {
    println!("--- RECOVERY MODE ---");
    let key = derive_key(senha);
    let mut full_compressed_stream = Vec::new();

    let mut current_img_path = PathBuf::from(primeira_imagem);
    let base_dir = current_img_path
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));

    // The recovery code doesn't know how many bits were used in the creation.
    // As we agreed in the prompt, we'll assume 2 bits as the default,
    // but ideally this would be a CLI argument as well if it were variable.

    let bits_leitura = 2;

    loop {
        println!("Processing: {:?}", current_img_path.file_name().unwrap());
        if !current_img_path.exists() {
            return Err(anyhow!(
                "Chain file not found: {:?}",
                current_img_path
            ));
        }

        let img = image::open(&current_img_path)
            .with_context(|| format!("Failed to open {:?}", current_img_path))?
            .to_rgba8();

        // 1. Read header size
        let size_bytes = extract_raw_bits(&img, bits_leitura, Some(4), 0);
        let enc_header_len = Cursor::new(size_bytes).read_u32::<BigEndian>()? as usize;

        // 2. Read Encrypted Header
        let header_offset_bits = 4 * 8;
        let enc_header =
            extract_raw_bits(&img, bits_leitura, Some(enc_header_len), header_offset_bits);

        // 3. Decipher Header
        let header_plain = decrypt_bytes(&enc_header, &key)?;
        let header: ChainHeader = bincode::deserialize(&header_plain)?;

        // 4. Read Chunk
        let chunk_offset_bits = header_offset_bits + (enc_header_len * 8);
        let enc_chunk_len = header.chunk_len as usize + 12 + 16;

        let enc_chunk =
            extract_raw_bits(&img, bits_leitura, Some(enc_chunk_len), chunk_offset_bits);
        let chunk_plain = decrypt_bytes(&enc_chunk, &key)?;
        full_compressed_stream.extend(chunk_plain);

        if !header.has_next {
            println!("End of chain detected.");
            break;
        }

        current_img_path = base_dir.join(&header.next_filename);
    }

    println!("Decompressing...");
    let raw_package = decompress_data(&full_compressed_stream)?;

    let mut cursor = Cursor::new(&raw_package);
    let name_len = cursor.read_u32::<BigEndian>()? as usize;

    let mut name_bytes = vec![0u8; name_len];
    cursor.read_exact(&mut name_bytes)?;
    let filename = String::from_utf8(name_bytes)?;

    let mut file_content = Vec::new();
    cursor.read_to_end(&mut file_content)?;

    let output_name = format!("RECOVERED_{}", filename);
    fs::write(&output_name, file_content)?;

    println!("SUCCESS! File saved as: {}", output_name);
    Ok(())
}

//--------------------------------------------------------------------------------
fn gerar_iscas(input_dir: &str, output_dir: &str, bits: u8) -> Result<()> {
    println!("--- GENERATING DECOYS (RECYCLED SOURCE) ---");

    if !Path::new(input_dir).exists() || !Path::new(output_dir).exists() {
        return Err(anyhow!("Directories not found."));
    }

    // Load source pool
    let imagens_originais: Vec<PathBuf> = fs::read_dir(input_dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map_or(false, is_valid_image))
        .collect();

    if imagens_originais.is_empty() {
        return Err(anyhow!("No source images to create decoys from."));
    }

    let mut rng = rand::thread_rng();
    
    // We will generate N decoys, where N = number of source images.
    // This scales logically. If user wants more, run command again.
    let target_count = imagens_originais.len();
    let mut generated_count = 0;

    println!("Generating {} new decoys based on random source picks...", target_count);

    for _ in 0..target_count {
        // 1. Pick ANY image from source (allows repetition)
        let img_path = imagens_originais.choose(&mut rng).unwrap();

        // 2. Generate Unique Random Name
        let nome_saida = loop {
            let candidate = generate_random_name();
            let path = Path::new(output_dir).join(&candidate);
            if !path.exists() {
                break candidate;
            }
        };

        let caminho_saida = Path::new(output_dir).join(&nome_saida);

        let img = image::open(img_path)
            .context("Failed to open image")?
            .to_rgba8();
        let (w, h) = img.dimensions();
        let capacidade = calcular_capacidade_chunk(w, h, bits, 150);

        if capacidade == 0 { continue; }

        // 3. Generate Noise (Simulation)
        let tamanho_lixo = rng.gen_range((capacidade / 2)..capacidade);
        let mut random_bytes = vec![0u8; tamanho_lixo];
        rng.fill(&mut random_bytes[..]);

        let fake_header_len = rng.gen_range(50..200) as u32;

        let mut final_blob = Vec::new();
        final_blob.write_u32::<BigEndian>(fake_header_len)?;
        final_blob.extend_from_slice(&random_bytes);

        // 4. Save
        let img_dyn = DynamicImage::ImageRgba8(img);
        if let Ok(stego_img) = embed_raw_bits(&img_dyn, &final_blob, bits) {
            stego_img.save(&caminho_saida)?;
            generated_count += 1;
            println!("Decoy created: {}", nome_saida);
        }
    }

    println!("Finished! {} decoys added.", generated_count);

    // Apply security measures
    scramble_creation_order(output_dir)?;
    sanitizar_metadados(output_dir)?;

    Ok(())
}

//---------------------------------------------------------------------------------------
fn scan_folder(dir: &str, password: &str) -> Result<()> {
    println!("--- SCANNER MODE ---");
    println!("Searching for chain start in '{}'...", dir);

    if !Path::new(dir).exists() {
        return Err(anyhow!("Folder not found"));
    }

    let imagens: Vec<PathBuf> = fs::read_dir(dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map_or(false, is_valid_image))
        .collect();

    let key = derive_key(password);
    let mut encontrou = false;

    // Try each image
    for img_path in imagens {
        // Try to read the header silently
        let result = try_decrypt_header(&img_path, &key);

        match result {
            Ok(header) => {
                // If decrypted successfully, check if it makes sense
                // Decoys with random trash will likely FAIL decryption (99.9% of the time)
                // or generate nonsense data. Bincode will fail if struct doesn't match.

                println!(
                    "\n[SUCCESS] Potential start found: {:?}",
                    img_path.file_name().unwrap()
                );
                println!(" -> Next file pointed to: '{}'", header.next_filename);
                println!(" -> Starting automatic recovery...\n");

                // Call normal recovery
                recuperar_cadeia(img_path.to_str().unwrap(), password)?;
                encontrou = true;
                break; // Stop after finding and recovering the first valid one
            }
            Err(_) => {
                // Silent failure: Wrong password, or it's a decoy, or not the start.
                // Just continue.
                print!(".");
                std::io::stdout().flush()?;
            }
        }
    }

    if !encontrou {
        println!("\n\nNo valid chain found with this password.");
        println!("Possibilities:");
        println!("1. Password is wrong.");
        println!("2. The starting image is not in this folder.");
        println!("3. All images are decoys.");
    }

    Ok(())
}

// Helper for the Scan to attempt to open without crashing
fn try_decrypt_header(path: &Path, key: &[u8; 32]) -> Result<ChainHeader> {
    let img = image::open(path)?.to_rgba8();
    // Try to read size
    let size_bytes = extract_raw_bits(&img, 2, Some(4), 0);
    let enc_len = Cursor::new(size_bytes).read_u32::<BigEndian>()? as usize;

    if enc_len == 0 || enc_len > 1000 {
        return Err(anyhow!("Invalid size"));
    }

    let enc_header = extract_raw_bits(&img, 2, Some(enc_len), 32);
    let plain = decrypt_bytes(&enc_header, key)?;

    let header: ChainHeader = bincode::deserialize(&plain)?;

    // CRITICAL CHECK:
    // If decrypted, but it's not the first file (sequence_number 0),
    // then it is not the start of the chain.
    if header.sequence_number != 0 {
        return Err(anyhow!(
            "Valid file found, but not the start of the chain (Seq: {})",
            header.sequence_number
        ));
    }

    Ok(header)
}

use chrono::{Duration, Local};
use filetime::{FileTime, set_file_times};

fn sanitizar_metadados(pasta: &str) -> Result<()> {
    println!("--- SANITIZING METADATA (TIMESTAMPS) ---");

    if !Path::new(pasta).exists() {
        return Ok(());
    }

    // 1. Collect all files
    let mut arquivos: Vec<PathBuf> = fs::read_dir(pasta)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();

    if arquivos.is_empty() {
        return Ok(());
    }

    println!("Shuffling timestamps of {} files...", arquivos.len());

    // 2. Shuffle processing order to ensure the
    // file system doesn't keep a sequential 'Last Access'
    let mut rng = rand::thread_rng();
    arquivos.shuffle(&mut rng);

    // 3. Define a base time window (e.g., Now)
    let agora = Local::now();

    for path in arquivos {
        // Generates a random delay between 0 and 10 days back
        let dias_atras = rng.gen_range(0..10);
        let segundos_atras = rng.gen_range(0..86400); // 24h

        let nova_data = agora - Duration::days(dias_atras) - Duration::seconds(segundos_atras);

        // Converts to filetime library format
        let timestamp = FileTime::from_unix_time(nova_data.timestamp(), 0);

        // Applies the new date to both 'Access Time' and 'Modification Time'
        // This overwrites the actual file creation date on disk (for sorting purposes)
        if let Err(e) = set_file_times(&path, timestamp, timestamp) {
            eprintln!(
                "Warning: Could not change date of {:?}: {}",
                path.file_name(),
                e
            );
        }
    }

    println!("Timestamps successfully altered. Chronological order destroyed.");
    Ok(())
}

// =================================================================================================
use std::thread;
// use std::time; // Adicione ou use o caminho completo abaixo

fn scramble_creation_order(dir: &str) -> Result<()> {
    println!("--- SCRAMBLING FILE CREATION ORDER ---");
    
    if !Path::new(dir).exists() {
        return Ok(());
    }

    // 1. Coletar caminhos
    let mut paths: Vec<PathBuf> = fs::read_dir(dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();

    if paths.is_empty() {
        return Ok(());
    }

    println!("Re-creating {} files in random order to reset 'Birth Time'...", paths.len());

    // 2. Embaralhar a lista
    let mut rng = rand::thread_rng();
    paths.shuffle(&mut rng);

    // 3. O Loop de "Ressurreição"
    for path in paths {
        // A. Ler conteúdo para memória RAM
        let content = fs::read(&path).context("Failed to read for scrambling")?;

        // B. Deletar o arquivo original
        fs::remove_file(&path).context("Failed to remove for scrambling")?;

        // C. Criar novo arquivo com O MESMO NOME e conteúdo
        fs::write(&path, &content).context("Failed to write back scrambled file")?;

        // D. Delay aleatório
        let delay_ms = rng.gen_range(1..10); 
        
        // --- CORREÇÃO AQUI ---
        // Usamos std::time::Duration explicitamente para evitar conflito com chrono
        thread::sleep(std::time::Duration::from_millis(delay_ms));
    }

    println!("Creation order successfully scrambled.");
    Ok(())
}
// ============================================================================================================================================

// # Linux/Mac:
//./target/release/esteganografia ocultar   --input-dir "/home/yugi/Imagens/minhas_fotos"   --file "programa"   --output-dir "/home/yugi/Imagens/saida_final"   --password "Eu gosto de usar frases longas 2026"

// # Recovery (both systems):
// ./target/release/esteganografia recuperar   --input-img "/home/yugi/Imagens/saida_final/JxEiVrg0.png"   --pass
// word "Eu gosto de usar frases longas 2026"
// SCAN
// ./target/release/esteganografia scan   --dir "/home/yugi/Imagens/saida_final"   --password "Eu gosto de usar frases longas 2026"

fn main() {
    let cli = Cli::parse();

    match cli.command {
        // Ocultar virou Hide
        Commands::Hide {
            input_dir,
            file,
            output_dir,
            password,
            bits,
        } => {
            if let Err(e) = ocultar_em_lote(&input_dir, &file, &output_dir, &password, bits) {
                eprintln!("Fatal error (Hide): {}", e);
            }
        }
        // Recuperar virou Recover
        Commands::Recover {
            input_img,
            password,
        } => {
            if let Err(e) = recuperar_cadeia(&input_img, &password) {
                eprintln!("Fatal error (Recover): {}", e);
            }
        }
        // GerarIscas virou Decoys
        Commands::Decoys {
            input_dir,
            output_dir,
            bits,
        } => {
            if let Err(e) = gerar_iscas(&input_dir, &output_dir, bits) {
                eprintln!("Error generating decoys: {}", e);
            }
        }
        // Scan continua Scan
        Commands::Scan { dir, password } => {
            if let Err(e) = scan_folder(&dir, &password) {
                eprintln!("Error (Scan): {}", e);
            }
        }
    }
}