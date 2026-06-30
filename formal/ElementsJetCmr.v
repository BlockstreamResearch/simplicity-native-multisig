From Coq Require Import List Lia.
From MultisigFormal Require Import ElementsJets SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  CMR constants for the Elements jets used by the multisig covenant.

  Source: /Volumes/Somebody/Desktop/Simp/simplicity/C/elements/primitiveJetNode.inc.
  The C file stores each CMR as eight big-endian uint32 words.  The definitions
  below spell the same 32 bytes directly, so Coq can check their byte range and
  256-bit length before they are used as the jet part of a CMR algebra.
*)

Definition elements_jet_cmr_bytes (j : ElementsJet) : list byte :=
  match j with
  | JAdd32 => [61; 118; 116; 70; 110; 214; 158; 29; 190; 220; 212; 128; 87; 169; 230; 40; 140; 34; 37; 50; 251; 197; 4; 128; 73; 146; 140; 251; 119; 248; 41; 217]
  | JBip0340Verify => [201; 196; 90; 138; 236; 134; 89; 20; 59; 254; 42; 246; 234; 212; 141; 78; 5; 66; 69; 58; 202; 232; 75; 155; 187; 151; 101; 107; 103; 11; 223; 221]
  | JBuildTapbranch => [203; 236; 249; 188; 225; 114; 197; 15; 88; 89; 81; 223; 240; 224; 82; 61; 177; 9; 229; 112; 37; 236; 55; 222; 44; 58; 116; 212; 166; 115; 242; 37]
  | JBuildTaptweak => [56; 116; 31; 128; 162; 191; 16; 248; 248; 114; 48; 119; 198; 116; 28; 190; 174; 45; 202; 200; 87; 144; 27; 129; 55; 37; 128; 111; 33; 137; 142; 227]
  | JCurrentIndex => [21; 225; 5; 31; 242; 63; 133; 28; 25; 19; 31; 13; 230; 237; 196; 136; 35; 118; 162; 87; 144; 219; 217; 16; 40; 36; 170; 34; 168; 137; 174; 132]
  | JCurrentScriptHash => [191; 175; 133; 132; 67; 206; 200; 51; 126; 55; 131; 157; 196; 17; 53; 2; 113; 132; 88; 12; 137; 33; 87; 206; 115; 4; 24; 192; 141; 94; 216; 56]
  | JEq1 => [96; 127; 107; 143; 93; 37; 184; 14; 5; 162; 191; 121; 214; 46; 135; 7; 153; 82; 44; 195; 227; 156; 233; 98; 87; 69; 82; 147; 249; 178; 178; 237]
  | JEq16 => [201; 150; 228; 43; 151; 154; 188; 83; 12; 194; 113; 99; 102; 113; 233; 32; 84; 135; 106; 30; 202; 237; 20; 51; 253; 97; 154; 37; 254; 109; 3; 173]
  | JEq256 => [119; 141; 21; 6; 199; 53; 210; 119; 107; 149; 15; 172; 239; 193; 89; 182; 120; 222; 192; 56; 40; 207; 2; 115; 238; 234; 100; 169; 218; 152; 193; 44]
  | JEq32 => [102; 211; 137; 3; 231; 59; 26; 19; 32; 198; 138; 74; 57; 112; 215; 31; 148; 186; 158; 43; 21; 22; 131; 153; 67; 251; 21; 228; 78; 191; 87; 251]
  | JIncrement32 => [84; 247; 87; 174; 167; 107; 199; 163; 159; 196; 61; 25; 184; 221; 86; 58; 104; 7; 223; 2; 119; 165; 111; 203; 80; 16; 137; 206; 125; 6; 119; 76]
  | JInputHash => [51; 9; 187; 70; 179; 21; 141; 35; 18; 79; 140; 237; 170; 161; 237; 59; 9; 168; 174; 254; 129; 33; 46; 17; 51; 85; 35; 182; 178; 7; 197; 68]
  | JInputScriptHash => [195; 22; 223; 33; 119; 142; 98; 65; 5; 202; 89; 144; 75; 146; 8; 226; 212; 35; 34; 139; 62; 177; 207; 104; 184; 236; 164; 123; 188; 123; 47; 243]
  | JLe32 => [222; 226; 154; 145; 101; 109; 122; 231; 61; 244; 149; 111; 216; 162; 198; 182; 39; 170; 181; 28; 17; 41; 249; 254; 127; 110; 211; 227; 71; 146; 199; 98]
  | JLeftPadLow16_32 => [33; 83; 127; 125; 143; 151; 242; 32; 60; 204; 176; 53; 239; 29; 70; 40; 158; 232; 170; 80; 240; 35; 96; 119; 208; 208; 178; 16; 112; 4; 64; 161]
  | JLeftPadLow8_32 => [61; 165; 241; 168; 201; 120; 25; 174; 126; 16; 185; 54; 79; 248; 73; 150; 208; 215; 62; 105; 138; 73; 218; 105; 31; 105; 162; 115; 37; 66; 1; 205]
  | JLt32 => [202; 176; 220; 91; 14; 203; 246; 210; 72; 22; 252; 32; 16; 252; 49; 25; 54; 99; 195; 6; 150; 141; 156; 238; 59; 0; 76; 11; 193; 132; 180; 120]
  | JNumInputs => [178; 40; 142; 186; 173; 203; 207; 206; 28; 99; 25; 100; 200; 107; 18; 125; 111; 145; 220; 101; 124; 89; 167; 251; 69; 62; 145; 17; 216; 116; 129; 245]
  | JOutputHash => [124; 177; 127; 143; 199; 161; 174; 78; 252; 227; 10; 20; 84; 229; 47; 133; 133; 33; 60; 208; 243; 103; 161; 39; 172; 39; 187; 151; 102; 234; 158; 238]
  | JSha256Ctx8Add2 => [139; 174; 62; 126; 30; 212; 220; 186; 110; 100; 90; 161; 67; 65; 187; 174; 13; 187; 58; 226; 27; 182; 61; 192; 48; 202; 14; 68; 122; 133; 126; 194]
  | JSha256Ctx8Add32 => [57; 35; 154; 67; 168; 75; 172; 111; 41; 105; 191; 169; 91; 254; 106; 4; 252; 186; 128; 146; 137; 89; 57; 241; 42; 28; 224; 226; 99; 33; 236; 16]
  | JSha256Ctx8Add64 => [253; 196; 52; 206; 131; 219; 220; 224; 120; 42; 163; 109; 65; 141; 239; 127; 153; 175; 130; 147; 175; 178; 158; 131; 159; 228; 148; 143; 98; 52; 247; 127]
  | JSha256Ctx8Finalize => [203; 186; 31; 29; 138; 151; 171; 77; 31; 169; 104; 110; 122; 238; 240; 102; 251; 91; 242; 144; 113; 110; 174; 16; 231; 11; 97; 153; 150; 197; 149; 148]
  | JSha256Ctx8Init => [165; 60; 118; 121; 227; 174; 3; 71; 212; 215; 145; 38; 167; 199; 228; 154; 192; 222; 201; 12; 223; 147; 87; 153; 205; 219; 88; 218; 143; 68; 150; 228]
  | JTapdataInit => [108; 103; 229; 193; 7; 53; 48; 94; 231; 222; 181; 154; 108; 106; 194; 239; 252; 171; 79; 247; 187; 71; 158; 167; 0; 129; 96; 110; 96; 72; 76; 167]
  | JVerify => [52; 62; 109; 193; 107; 63; 82; 232; 62; 59; 76; 204; 153; 184; 198; 249; 106; 7; 79; 227; 153; 50; 122; 243; 100; 188; 40; 94; 41; 151; 69; 162]
  end.

Definition elements_jet_cmr_bits (j : ElementsJet) : CmrBits :=
  bytes_to_bits (elements_jet_cmr_bytes j).

Theorem elements_jet_cmr_bytes_length :
  forall j,
    length (elements_jet_cmr_bytes j) = 32.
Proof.
  destruct j; vm_compute; reflexivity.
Qed.

Theorem elements_jet_cmr_bytes_in_range :
  forall j,
    Forall (fun b => b <= 255) (elements_jet_cmr_bytes j).
Proof.
  destruct j; vm_compute; repeat constructor; lia.
Qed.

Theorem elements_jet_cmr_bits_length :
  forall j,
    length (elements_jet_cmr_bits j) = 256.
Proof.
  destruct j; vm_compute; reflexivity.
Qed.

Theorem elements_jet_cmr_bits_well_formed :
  forall j,
    cmr_bits_well_formed (elements_jet_cmr_bits j) = true.
Proof.
  destruct j; vm_compute; reflexivity.
Qed.

Definition with_elements_jet_cmr (alg : CmrAlgebra) : CmrAlgebra := {|
  cmr_iden := cmr_iden alg;
  cmr_unit := cmr_unit alg;
  cmr_injl := cmr_injl alg;
  cmr_injr := cmr_injr alg;
  cmr_take := cmr_take alg;
  cmr_drop := cmr_drop alg;
  cmr_comp := cmr_comp alg;
  cmr_case := cmr_case alg;
  cmr_pair := cmr_pair alg;
  cmr_disconnect := cmr_disconnect alg;
  cmr_witness := cmr_witness alg;
  cmr_fail := cmr_fail alg;
  cmr_jet := elements_jet_cmr_bits;
  cmr_word := cmr_word alg
|}.
