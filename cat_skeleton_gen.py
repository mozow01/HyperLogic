import re
import os
import glob

# Célmappa és kimeneti fájl
CAT_FOLDER = "./theories/Cat"
OUTPUT_FILE = "cat_skeleton.txt"

# Regex a bizonyítások felismeréséhez
proof_pattern = re.compile(r'Proof\b.*?\.(?:(?:\s+)|(?:\n))+(?:.*?\b(?:Qed|Defined|Admitted)\.)', re.DOTALL)

def clean_coq_proofs(content):
    # Bizonyítások lecserélése
    cleaned = proof_pattern.sub('Proof. Admitted.', content)
    # Felesleges üres sorok eltávolítása
    cleaned = re.sub(r'\n\s*\n\s*\n', '\n\n', cleaned)
    return cleaned

def generate_cat_skeleton():
    if not os.path.exists(CAT_FOLDER):
        print(f"Hiba: Nem találom a '{CAT_FOLDER}' mappát. Biztos jó helyen futtatod?")
        return

    # Csak a Cat mappában lévő .v fájlokat keressük
    cat_files = glob.glob(os.path.join(CAT_FOLDER, "*.v"))
    
    if not cat_files:
        print("Nem találtam .v fájlokat a Cat mappában!")
        return

    print(f"Talált fájlok a Cat mappában: {len(cat_files)} db")
    
    with open(OUTPUT_FILE, 'w', encoding='utf-8') as outfile:
        outfile.write("--- HYPERLOGIC PROJECT: CAT FOLDER SKELETON ---\n\n")
        
        for file_path in sorted(cat_files):
            # Fájlnév kinyerése
            filename = os.path.basename(file_path)
            
            # Fájl beolvasása és tisztítása
            with open(file_path, 'r', encoding='utf-8') as infile:
                content = infile.read()
            cleaned_content = clean_coq_proofs(content)
            
            # Elválasztó és fájlnév beírása, hogy a Gemini tudja, melyik fájlt látja
            outfile.write(f"{'='*40}\n")
            outfile.write(f"FILE: theories/Cat/{filename}\n")
            outfile.write(f"MODULE: HyperLogic.Cat.{filename.replace('.v', '')}\n")
            outfile.write(f"{'='*40}\n\n")
            
            # Tiszta kód beírása
            outfile.write(cleaned_content)
            outfile.write("\n\n")

    print(f"Siker! A fájl elkészült: {OUTPUT_FILE}")

if __name__ == "__main__":
    generate_cat_skeleton()
