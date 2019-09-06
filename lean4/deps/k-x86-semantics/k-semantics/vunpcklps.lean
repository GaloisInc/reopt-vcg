def vunpcklps1 : instruction :=
  definst "vunpcklps" $ do
    pattern fun (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) (v_3295 : reg (bv 128)) => do
      v_7633 <- getRegister v_3293;
      v_7635 <- getRegister v_3294;
      setRegister (lhs.of_reg v_3295) (concat (concat (concat (extract v_7633 64 96) (extract v_7635 64 96)) (extract v_7633 96 128)) (extract v_7635 96 128));
      pure ()
    pat_end;
    pattern fun (v_3304 : reg (bv 256)) (v_3305 : reg (bv 256)) (v_3306 : reg (bv 256)) => do
      v_7648 <- getRegister v_3304;
      v_7650 <- getRegister v_3305;
      setRegister (lhs.of_reg v_3306) (concat (concat (concat (concat (extract v_7648 64 96) (extract v_7650 64 96)) (extract v_7648 96 128)) (extract v_7650 96 128)) (concat (concat (concat (extract v_7648 192 224) (extract v_7650 192 224)) (extract v_7648 224 256)) (extract v_7650 224 256)));
      pure ()
    pat_end;
    pattern fun (v_3287 : Mem) (v_3288 : reg (bv 128)) (v_3289 : reg (bv 128)) => do
      v_13489 <- evaluateAddress v_3287;
      v_13490 <- load v_13489 16;
      v_13492 <- getRegister v_3288;
      setRegister (lhs.of_reg v_3289) (concat (concat (concat (extract v_13490 64 96) (extract v_13492 64 96)) (extract v_13490 96 128)) (extract v_13492 96 128));
      pure ()
    pat_end;
    pattern fun (v_3298 : Mem) (v_3299 : reg (bv 256)) (v_3300 : reg (bv 256)) => do
      v_13500 <- evaluateAddress v_3298;
      v_13501 <- load v_13500 32;
      v_13503 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3300) (concat (concat (concat (concat (extract v_13501 64 96) (extract v_13503 64 96)) (extract v_13501 96 128)) (extract v_13503 96 128)) (concat (concat (concat (extract v_13501 192 224) (extract v_13503 192 224)) (extract v_13501 224 256)) (extract v_13503 224 256)));
      pure ()
    pat_end
