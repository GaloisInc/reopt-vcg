def vmovmskpd : instruction :=
  definst "vmovmskpd" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 30 0) (concat v_3 v_4));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 62 0) (concat v_3 v_4));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_5 : expression (bv 8)) <- eval (extract (add (concat (expression.bv_nat 7 0) (concat v_3 v_4)) (concat (expression.bv_nat 7 0) (concat v_3 v_4))) 1 9);
      (v_6 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_7 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_8 : expression (bv 8)) <- eval (extract (add (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 7 0) (concat v_6 v_7))) 1 9);
      (v_9 : expression (bv 16)) <- eval (extract (add (concat (expression.bv_nat 9 0) v_8) (concat (expression.bv_nat 9 0) v_5)) 1 17);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) v_9);
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_5 : expression (bv 8)) <- eval (extract (add (concat (expression.bv_nat 7 0) (concat v_3 v_4)) (concat (expression.bv_nat 7 0) (concat v_3 v_4))) 1 9);
      (v_6 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_7 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_8 : expression (bv 8)) <- eval (extract (add (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 7 0) (concat v_6 v_7))) 1 9);
      (v_9 : expression (bv 16)) <- eval (extract (add (concat (expression.bv_nat 9 0) v_8) (concat (expression.bv_nat 9 0) v_5)) 1 17);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) v_9);
      pure ()
    pat_end
