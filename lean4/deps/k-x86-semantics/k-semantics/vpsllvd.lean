def vpsllvd1 : instruction :=
  definst "vpsllvd" $ do
    pattern fun (v_3184 : reg (bv 128)) (v_3185 : reg (bv 128)) (v_3186 : reg (bv 128)) => do
      v_7887 <- getRegister v_3185;
      v_7889 <- getRegister v_3184;
      setRegister (lhs.of_reg v_3186) (concat (extract (shl (extract v_7887 0 32) (extract v_7889 0 32)) 0 32) (concat (extract (shl (extract v_7887 32 64) (extract v_7889 32 64)) 0 32) (concat (extract (shl (extract v_7887 64 96) (extract v_7889 64 96)) 0 32) (extract (shl (extract v_7887 96 128) (extract v_7889 96 128)) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3195 : reg (bv 256)) (v_3196 : reg (bv 256)) (v_3197 : reg (bv 256)) => do
      v_7914 <- getRegister v_3196;
      v_7916 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3197) (concat (extract (shl (extract v_7914 0 32) (extract v_7916 0 32)) 0 32) (concat (extract (shl (extract v_7914 32 64) (extract v_7916 32 64)) 0 32) (concat (extract (shl (extract v_7914 64 96) (extract v_7916 64 96)) 0 32) (concat (extract (shl (extract v_7914 96 128) (extract v_7916 96 128)) 0 32) (concat (extract (shl (extract v_7914 128 160) (extract v_7916 128 160)) 0 32) (concat (extract (shl (extract v_7914 160 192) (extract v_7916 160 192)) 0 32) (concat (extract (shl (extract v_7914 192 224) (extract v_7916 192 224)) 0 32) (extract (shl (extract v_7914 224 256) (extract v_7916 224 256)) 0 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3178 : Mem) (v_3179 : reg (bv 128)) (v_3180 : reg (bv 128)) => do
      v_14026 <- getRegister v_3179;
      v_14028 <- evaluateAddress v_3178;
      v_14029 <- load v_14028 16;
      setRegister (lhs.of_reg v_3180) (concat (extract (shl (extract v_14026 0 32) (extract v_14029 0 32)) 0 32) (concat (extract (shl (extract v_14026 32 64) (extract v_14029 32 64)) 0 32) (concat (extract (shl (extract v_14026 64 96) (extract v_14029 64 96)) 0 32) (extract (shl (extract v_14026 96 128) (extract v_14029 96 128)) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3189 : Mem) (v_3190 : reg (bv 256)) (v_3191 : reg (bv 256)) => do
      v_14049 <- getRegister v_3190;
      v_14051 <- evaluateAddress v_3189;
      v_14052 <- load v_14051 32;
      setRegister (lhs.of_reg v_3191) (concat (extract (shl (extract v_14049 0 32) (extract v_14052 0 32)) 0 32) (concat (extract (shl (extract v_14049 32 64) (extract v_14052 32 64)) 0 32) (concat (extract (shl (extract v_14049 64 96) (extract v_14052 64 96)) 0 32) (concat (extract (shl (extract v_14049 96 128) (extract v_14052 96 128)) 0 32) (concat (extract (shl (extract v_14049 128 160) (extract v_14052 128 160)) 0 32) (concat (extract (shl (extract v_14049 160 192) (extract v_14052 160 192)) 0 32) (concat (extract (shl (extract v_14049 192 224) (extract v_14052 192 224)) 0 32) (extract (shl (extract v_14049 224 256) (extract v_14052 224 256)) 0 32))))))));
      pure ()
    pat_end
