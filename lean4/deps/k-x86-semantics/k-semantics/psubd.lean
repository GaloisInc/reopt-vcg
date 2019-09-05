def psubd1 : instruction :=
  definst "psubd" $ do
    pattern fun (v_3153 : reg (bv 128)) (v_3154 : reg (bv 128)) => do
      v_8016 <- getRegister v_3154;
      v_8018 <- getRegister v_3153;
      setRegister (lhs.of_reg v_3154) (concat (sub (extract v_8016 0 32) (extract v_8018 0 32)) (concat (sub (extract v_8016 32 64) (extract v_8018 32 64)) (concat (sub (extract v_8016 64 96) (extract v_8018 64 96)) (sub (extract v_8016 96 128) (extract v_8018 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3149 : reg (bv 128)) => do
      v_14494 <- getRegister v_3149;
      v_14496 <- evaluateAddress v_3150;
      v_14497 <- load v_14496 16;
      setRegister (lhs.of_reg v_3149) (concat (sub (extract v_14494 0 32) (extract v_14497 0 32)) (concat (sub (extract v_14494 32 64) (extract v_14497 32 64)) (concat (sub (extract v_14494 64 96) (extract v_14497 64 96)) (sub (extract v_14494 96 128) (extract v_14497 96 128)))));
      pure ()
    pat_end
