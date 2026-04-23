import re
import os
import glob

# Beállítások
source_folder = "./theories"  # A te projektedben itt vannak a .v fájlok
output_folder = "./skeleton"   # A szkript ide fogja gyártani a tiszta fájlokat

if not os.path.exists(output_folder):
    os.makedirs(output_folder)

# Ez a minta keresi meg a bizonyításokat
proof_pattern = re.compile(r'Proof\b.*?\.(?:(?:\s+)|(?:\n))+(?:.*?\b(?:Qed|Defined|Admitted)\.)', re.DOTALL)

def strip_coq_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    # Kicseréljük a bizonyítást egy rövid Admitted-re
    stripped = proof_pattern.sub('Proof. Admitted.', content)
    # Túl sok üres sor és felesleges szóközök takarítása a végén
    stripped = re.sub(r'[ \t]+$', '', stripped, flags=re.MULTILINE)
    stripped = re.sub(r'\n\s*\n\s*\n', '\n\n', stripped)
    return stripped

# Végigmegyünk az összes .v fájlon a theories mappában
v_files = glob.glob(os.path.join(source_folder, "**/*.v"), recursive=True)

for file_path in v_files:
    relative_path = os.path.relpath(file_path, source_folder)
    dest_path = os.path.join(output_folder, relative_path)
    
    # Létrehozza az alkönyvtárakat (pl. Cat, Logic) a skeleton mappán belül is
    os.makedirs(os.path.dirname(dest_path), exist_ok=True)
    
    clean_code = strip_coq_file(file_path)
    
    with open(dest_path, 'w', encoding='utf-8') as f:
        f.write(clean_code)

print(f"Kész! {len(v_files)} fájl tisztítva a '{output_folder}' mappába.")