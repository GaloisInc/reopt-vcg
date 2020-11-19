def movmskps : instruction :=
  definst "movmskps" $ do
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
    pat_end
