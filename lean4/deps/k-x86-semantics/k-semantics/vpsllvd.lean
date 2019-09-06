def vpsllvd1 : instruction :=
  definst "vpsllvd" $ do
    pattern fun (v_3211 : reg (bv 128)) (v_3212 : reg (bv 128)) (v_3213 : reg (bv 128)) => do
      v_7914 <- getRegister v_3212;
      v_7916 <- getRegister v_3211;
      setRegister (lhs.of_reg v_3213) (concat (extract (shl (extract v_7914 0 32) (extract v_7916 0 32)) 0 32) (concat (extract (shl (extract v_7914 32 64) (extract v_7916 32 64)) 0 32) (concat (extract (shl (extract v_7914 64 96) (extract v_7916 64 96)) 0 32) (extract (shl (extract v_7914 96 128) (extract v_7916 96 128)) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3222 : reg (bv 256)) (v_3223 : reg (bv 256)) (v_3224 : reg (bv 256)) => do
      v_7941 <- getRegister v_3223;
      v_7943 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3224) (concat (extract (shl (extract v_7941 0 32) (extract v_7943 0 32)) 0 32) (concat (extract (shl (extract v_7941 32 64) (extract v_7943 32 64)) 0 32) (concat (extract (shl (extract v_7941 64 96) (extract v_7943 64 96)) 0 32) (concat (extract (shl (extract v_7941 96 128) (extract v_7943 96 128)) 0 32) (concat (extract (shl (extract v_7941 128 160) (extract v_7943 128 160)) 0 32) (concat (extract (shl (extract v_7941 160 192) (extract v_7943 160 192)) 0 32) (concat (extract (shl (extract v_7941 192 224) (extract v_7943 192 224)) 0 32) (extract (shl (extract v_7941 224 256) (extract v_7943 224 256)) 0 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 128)) (v_3207 : reg (bv 128)) => do
      v_14053 <- getRegister v_3206;
      v_14055 <- evaluateAddress v_3205;
      v_14056 <- load v_14055 16;
      setRegister (lhs.of_reg v_3207) (concat (extract (shl (extract v_14053 0 32) (extract v_14056 0 32)) 0 32) (concat (extract (shl (extract v_14053 32 64) (extract v_14056 32 64)) 0 32) (concat (extract (shl (extract v_14053 64 96) (extract v_14056 64 96)) 0 32) (extract (shl (extract v_14053 96 128) (extract v_14056 96 128)) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3216 : Mem) (v_3217 : reg (bv 256)) (v_3218 : reg (bv 256)) => do
      v_14076 <- getRegister v_3217;
      v_14078 <- evaluateAddress v_3216;
      v_14079 <- load v_14078 32;
      setRegister (lhs.of_reg v_3218) (concat (extract (shl (extract v_14076 0 32) (extract v_14079 0 32)) 0 32) (concat (extract (shl (extract v_14076 32 64) (extract v_14079 32 64)) 0 32) (concat (extract (shl (extract v_14076 64 96) (extract v_14079 64 96)) 0 32) (concat (extract (shl (extract v_14076 96 128) (extract v_14079 96 128)) 0 32) (concat (extract (shl (extract v_14076 128 160) (extract v_14079 128 160)) 0 32) (concat (extract (shl (extract v_14076 160 192) (extract v_14079 160 192)) 0 32) (concat (extract (shl (extract v_14076 192 224) (extract v_14079 192 224)) 0 32) (extract (shl (extract v_14076 224 256) (extract v_14079 224 256)) 0 32))))))));
      pure ()
    pat_end
