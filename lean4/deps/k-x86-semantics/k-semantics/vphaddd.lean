def vphaddd1 : instruction :=
  definst "vphaddd" $ do
    pattern fun (v_3240 : reg (bv 128)) (v_3241 : reg (bv 128)) (v_3242 : reg (bv 128)) => do
      v_8690 <- getRegister v_3240;
      v_8698 <- getRegister v_3241;
      setRegister (lhs.of_reg v_3242) (concat (concat (concat (add (extract v_8690 0 32) (extract v_8690 32 64)) (add (extract v_8690 64 96) (extract v_8690 96 128))) (add (extract v_8698 0 32) (extract v_8698 32 64))) (add (extract v_8698 64 96) (extract v_8698 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3251 : reg (bv 256)) (v_3252 : reg (bv 256)) (v_3253 : reg (bv 256)) => do
      v_8713 <- getRegister v_3251;
      v_8721 <- getRegister v_3252;
      setRegister (lhs.of_reg v_3253) (concat (concat (concat (concat (add (extract v_8713 0 32) (extract v_8713 32 64)) (add (extract v_8713 64 96) (extract v_8713 96 128))) (add (extract v_8721 0 32) (extract v_8721 32 64))) (add (extract v_8721 64 96) (extract v_8721 96 128))) (concat (concat (concat (add (extract v_8713 128 160) (extract v_8713 160 192)) (add (extract v_8713 192 224) (extract v_8713 224 256))) (add (extract v_8721 128 160) (extract v_8721 160 192))) (add (extract v_8721 192 224) (extract v_8721 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3235 : Mem) (v_3236 : reg (bv 128)) (v_3237 : reg (bv 128)) => do
      v_17110 <- evaluateAddress v_3235;
      v_17111 <- load v_17110 16;
      v_17119 <- getRegister v_3236;
      setRegister (lhs.of_reg v_3237) (concat (concat (concat (add (extract v_17111 0 32) (extract v_17111 32 64)) (add (extract v_17111 64 96) (extract v_17111 96 128))) (add (extract v_17119 0 32) (extract v_17119 32 64))) (add (extract v_17119 64 96) (extract v_17119 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3246 : Mem) (v_3247 : reg (bv 256)) (v_3248 : reg (bv 256)) => do
      v_17129 <- evaluateAddress v_3246;
      v_17130 <- load v_17129 32;
      v_17138 <- getRegister v_3247;
      setRegister (lhs.of_reg v_3248) (concat (concat (concat (concat (add (extract v_17130 0 32) (extract v_17130 32 64)) (add (extract v_17130 64 96) (extract v_17130 96 128))) (add (extract v_17138 0 32) (extract v_17138 32 64))) (add (extract v_17138 64 96) (extract v_17138 96 128))) (concat (concat (concat (add (extract v_17130 128 160) (extract v_17130 160 192)) (add (extract v_17130 192 224) (extract v_17130 224 256))) (add (extract v_17138 128 160) (extract v_17138 160 192))) (add (extract v_17138 192 224) (extract v_17138 224 256))));
      pure ()
    pat_end
