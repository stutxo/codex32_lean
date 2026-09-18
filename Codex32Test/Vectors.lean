/-
Official BIP 93 fixtures, transcribed from spec/bip-0093.mediawiki.
Every distinct valid string, every padding alternative, and every invalid string
is retained verbatim (including original case). Xprvs are informational only:
BIP 32 key derivation is outside this Codex32 implementation.
-/

namespace Codex32.Vectors

structure SecretVector where
  label : String
  encoded : String
  hex : String
  padding : Nat
  deriving Repr

structure InvalidVector where
  category : String
  encoded : String
  deriving Repr

def vector2a : String :=
  "MS12NAMEA320ZYXWVUTSRQPNMLKJHGFEDCAXRPP870HKKQRM"

def vector2c : String :=
  "MS12NAMECACDEFGHJKLMNPQRSTUVWXYZ023FTR2GDZMPY6PN"

def vector2d : String :=
  "MS12NAMEDLL4F8JLH4E5VDVULDLFXU2JHDNLSM97XVENRXEG"

def vector2s : String :=
  "MS12NAMES6XQGUZTTXKEQNJSJZV4JV3NZ5K3KWGSPHUH6EVW"

def vector3s : String :=
  "ms13cashsllhdmn9m42vcsamx24zrxgs3qqjzqud4m0d6nln"

def vector3a : String :=
  "ms13casha320zyxwvutsrqpnmlkjhgfedca2a8d0zehn8a0t"

def vector3c : String :=
  "ms13cashcacdefghjklmnpqrstuvwxyz023949xq35my48dr"

def vector3d : String :=
  "ms13cashd0wsedstcdcts64cd7wvy4m90lm28w4ffupqs7rm"

def vector3e : String :=
  "ms13casheekgpemxzshcrmqhaydlp6yhms3ws7320xyxsar9"

def vector3f : String :=
  "ms13cashf8jh6sdrkpyrsp5ut94pj8ktehhw2hfvyrj48704"

def secrets : List SecretVector := [
  { label := "vector 1"
    encoded := "ms10testsxxxxxxxxxxxxxxxxxxxxxxxxxx4nzvca9cmczlw"
    hex := "318c6318c6318c6318c6318c6318c631"
    padding := 2 },
  { label := "vector 2"
    encoded := "MS12NAMES6XQGUZTTXKEQNJSJZV4JV3NZ5K3KWGSPHUH6EVW"
    hex := "d1808e096b35b209ca12132b264662a5"
    padding := 2 },
  { label := "vector 3 padding 0"
    encoded := "ms13cashsllhdmn9m42vcsamx24zrxgs3qqjzqud4m0d6nln"
    hex := "ffeeddccbbaa99887766554433221100"
    padding := 0 },
  { label := "vector 3 padding 1"
    encoded := "ms13cashsllhdmn9m42vcsamx24zrxgs3qpte35dvzkjpt0r"
    hex := "ffeeddccbbaa99887766554433221100"
    padding := 1 },
  { label := "vector 3 padding 2"
    encoded := "ms13cashsllhdmn9m42vcsamx24zrxgs3qzfatvdwq5692k6"
    hex := "ffeeddccbbaa99887766554433221100"
    padding := 2 },
  { label := "vector 3 padding 3"
    encoded := "ms13cashsllhdmn9m42vcsamx24zrxgs3qrsx6ydhed97jx2"
    hex := "ffeeddccbbaa99887766554433221100"
    padding := 3 },
  { label := "vector 4 padding 0"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqqtum9pgv99ycma"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 0 },
  { label := "vector 4 padding 1"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqpj82dp34u6lqtd"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 1 },
  { label := "vector 4 padding 2"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqzsrs4pnh7jmpj5"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 2 },
  { label := "vector 4 padding 3"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqrfcpap2w8dqezy"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 3 },
  { label := "vector 4 padding 4"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqy5tdvphn6znrf0"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 4 },
  { label := "vector 4 padding 5"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyq9dsuypw2ragmel"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 5 },
  { label := "vector 4 padding 6"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqx05xupvgp4v6qx"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 6 },
  { label := "vector 4 padding 7"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyq8k0h5p43c2hzsk"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 7 },
  { label := "vector 4 padding 8"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqgum7hplmjtr8ks"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 8 },
  { label := "vector 4 padding 9"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqf9q0lpxzt5clxq"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 9 },
  { label := "vector 4 padding 10"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyq28y48pyqfuu7le"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 10 },
  { label := "vector 4 padding 11"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqt7ly0paesr8x0f"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 11 },
  { label := "vector 4 padding 12"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqvrvg7pqydv5uyz"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 12 },
  { label := "vector 4 padding 13"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqd6hekpea5n0y5j"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 13 },
  { label := "vector 4 padding 14"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyqwcnrwpmlkmt9dt"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 14 },
  { label := "vector 4 padding 15"
    encoded := "ms10leetsllhdmn9m42vcsamx24zrxgs3qrl7ahwvhw4fnzrhve25gvezzyq0pgjxpzx0ysaam"
    hex := "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"
    padding := 15 },
  { label := "vector 5"
    encoded := "MS100C8VSM32ZXFGUHPCHTLUPZRY9X8GF2TVDW0S3JN54KHCE6MUA7LQPZYGSFJD6AN074RXVCEMLH8WU3TK925ACDEFGHJKLMNPQRSTUVWXY06FHPV80UNDVARHRAK"
    hex := "dc5423251cb87175ff8110c8531d0952d8d73e1194e95b5f19d6f9df7c01111104c9baecdfea8cccc677fb9ddc8aec5553b86e528bcadfdcc201c17c638c47e9"
    padding := 1 },
  { label := "vector 6"
    encoded := "ms10seedsqqqsyqcyq5rqwzqfpg9scrgwpugpzysn9vaqzzvs20xnl"
    hex := "000102030405060708090a0b0c0d0e0f10111213"
    padding := 0 },
  { label := "vector 7"
    encoded := "ms10seedsyqsjygeyy5nzw2pf9g4jctfw9ucrzv3nxs6nvdau84gz0632s0xs"
    hex := "202122232425262728292a2b2c2d2e2f3031323334353637"
    padding := 5 },
  { label := "vector 8"
    encoded := "ms10seedsgpq5ys6yg4rywjzfff95cn2wfag9z5jn2324v46ct9d9hrcduqw8c3lccl"
    hex := "404142434445464748494a4b4c4d4e4f505152535455565758595a5b"
    padding := 1 }
]

def validShares : List String := [
  vector2a, vector2c, vector2d,
  vector3a, vector3c, vector3d, vector3e, vector3f
]

def validStrings : List String := secrets.map (·.encoded) ++ validShares

def invalid : List InvalidVector := [
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxve740yyge2ghq" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxve740yyge2ghp" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxlk3yepcstwr" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxx6pgnv7jnpcsp" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxx0cpvr7n4geq" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxm5252y7d3lr" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxrd9sukzl05ej" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxc55srw5jrm0" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxgc7rwhtudwc" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxx4gy22afwghvs" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxme084q0vpht7pe0" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxme084q0vpht7pew" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxqyadsp3nywm8a" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxzvg7ar4hgaejk" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxcznau0advgxqe" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxch3jrc6j5040j" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx52gxl6ppv40mcv" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx7g4g2nhhle8fk" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx63m45uj8ss4x8" },
  { category := "incorrect checksum", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxy4r708q7kg65x" },
  { category := "wrong checksum variant", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxurfvwmdcmymdufv" },
  { category := "wrong checksum variant", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxcwm4re8fs78vn" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxwqey9rfs6smenxa" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxw0a4c70rfefn4" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxk4pavy5n46nea" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxx9lrwar5zwng4w" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxr335l5tv88js3" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxvu7q9nz8p7dj68v" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxpq6k542scdxndq3" },
  { category := "improper length", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxkmfw6jm270mz6ej" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxzhddxw99w7xws" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxx42cux6um92rz" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxarja5kqukdhy9" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxky0ua3ha84qk8" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx9eheesxadh2n2n9" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx9llwmgesfulcj2z" },
  { category := "improper length", encoded := "ms12fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx02ev7caq6n9fgkf" },
  { category := "zero threshold at non-secret index", encoded := "ms10fauxxxxxxxxxxxxxxxxxxxxxxxxxxxx0z26tfn0ulw3p" },
  { category := "non-digit threshold", encoded := "ms1fauxxxxxxxxxxxxxxxxxxxxxxxxxxxxxda3kr3s0s2swg" },
  { category := "prefix or separator", encoded := "0fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "prefix or separator", encoded := "10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "prefix or separator", encoded := "ms0fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "prefix or separator", encoded := "m10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "prefix or separator", encoded := "s10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "prefix or separator", encoded := "0fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxhkd4f70m8lgws" },
  { category := "prefix or separator", encoded := "10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxhkd4f70m8lgws" },
  { category := "prefix or separator", encoded := "m10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxx8t28z74x8hs4l" },
  { category := "prefix or separator", encoded := "s10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxh9d0fhnvfyx3x" },
  { category := "mixed case", encoded := "Ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "mS10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "MS10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "ms10FAUXsxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "ms10fauxSxxxxxxxxxxxxxxxxxxxxxxxxxxuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "ms10fauxsXXXXXXXXXXXXXXXXXXXXXXXXXXuqxkk05lyf3x2" },
  { category := "mixed case", encoded := "ms10fauxsxxxxxxxxxxxxxxxxxxxxxxxxxxUQXKK05LYF3X2" }
]

/-- Published BIP 32 results, preserved without implementing BIP 32. -/
def masterNodeXprvs : List String := [
  "xprv9s21ZrQH143K3taPNekMd9oV5K6szJ8ND7vVh6fxicRUMDcChr3bFFzuxY8qP3xFFBL6DWc2uEYCfBFZ2nFWbAqKPhtCLRjgv78EZJDEfpL",
  "xprv9s21ZrQH143K2NkobdHxXeyFDqE44nJYvzLFtsriatJNWMNKznGoGgW5UMTL4fyWtajnMYb5gEc2CgaKhmsKeskoi9eTimpRv2N11THhPTU",
  "xprv9s21ZrQH143K266qUcrDyYJrSG7KA3A7sE5UHndYRkFzsPQ6xwUhEGK1rNuyyA57Vkc1Ma6a8boVqcKqGNximmAe9L65WsYNcNitKRPnABd",
  "xprv9s21ZrQH143K3s41UCWxXTsU4TRrhkpD1t21QJETan3hjo8DP5LFdFcB5eaFtV8x6Y9aZotQyP8KByUjgLTbXCUjfu2iosTbMv98g8EQoqr",
  "xprv9s21ZrQH143K4UYT4rP3TZVKKbmRVmfRqTx9mG2xCy2JYipZbkLV8rwvBXsUbEv9KQiUD7oED1Wyi9evZzUn2rqK9skRgPkNaAzyw3YrpJN"
]

end Codex32.Vectors
