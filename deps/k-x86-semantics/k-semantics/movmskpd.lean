def movmskpd : instruction :=
  definst "movmskpd" $ do
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
    pat_end
