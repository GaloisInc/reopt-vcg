def psrlq1 : instruction :=
  definst "psrlq" $ do
    pattern fun (v_3113 : imm int) (v_3112 : reg (bv 128)) => do
      v_7853 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3113 8 8));
      v_7855 <- getRegister v_3112;
      setRegister (lhs.of_reg v_3112) (mux (ugt v_7853 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7855 0 64) v_7853) (lshr (extract v_7855 64 128) v_7853)));
      pure ()
    pat_end;
    pattern fun (v_3121 : reg (bv 128)) (v_3122 : reg (bv 128)) => do
      v_7867 <- getRegister v_3121;
      v_7868 <- eval (extract v_7867 64 128);
      v_7870 <- getRegister v_3122;
      setRegister (lhs.of_reg v_3122) (mux (ugt v_7868 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7870 0 64) v_7868) (lshr (extract v_7870 64 128) v_7868)));
      pure ()
    pat_end;
    pattern fun (v_3118 : Mem) (v_3117 : reg (bv 128)) => do
      v_14384 <- evaluateAddress v_3118;
      v_14385 <- load v_14384 16;
      v_14386 <- eval (extract v_14385 64 128);
      v_14388 <- getRegister v_3117;
      setRegister (lhs.of_reg v_3117) (mux (ugt v_14386 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14388 0 64) v_14386) (lshr (extract v_14388 64 128) v_14386)));
      pure ()
    pat_end
