def vmovmskps : instruction :=
  definst "vmovmskps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 28 0) (concat v_3 (concat v_4 (concat v_5 v_6))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 60 0) (concat v_3 (concat v_4 (concat v_5 v_6))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_7 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_8 : expression (bv 1)) <- eval (extract v_2 160 161);
      (v_9 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_10 : expression (bv 1)) <- eval (extract v_2 224 225);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 24 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 v_10))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_5 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_6 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_7 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_8 : expression (bv 1)) <- eval (extract v_2 160 161);
      (v_9 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_10 : expression (bv 1)) <- eval (extract v_2 224 225);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 56 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 v_10))))))));
      pure ()
    pat_end
