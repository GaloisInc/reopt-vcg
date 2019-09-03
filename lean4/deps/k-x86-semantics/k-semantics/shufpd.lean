def shufpd1 : instruction :=
  definst "shufpd" $ do
    pattern fun (v_3048 : imm int) (v_3050 : reg (bv 128)) (v_3051 : reg (bv 128)) => do
      v_6657 <- eval (handleImmediateWithSignExtend v_3048 8 8);
      v_6660 <- getRegister v_3050;
      v_6666 <- getRegister v_3051;
      setRegister (lhs.of_reg v_3051) (concat (mux (eq (extract v_6657 6 7) (expression.bv_nat 1 1)) (extract v_6660 0 64) (extract v_6660 64 128)) (mux (eq (extract v_6657 7 8) (expression.bv_nat 1 1)) (extract v_6666 0 64) (extract v_6666 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3043 : imm int) (v_3044 : Mem) (v_3045 : reg (bv 128)) => do
      v_10211 <- eval (handleImmediateWithSignExtend v_3043 8 8);
      v_10214 <- evaluateAddress v_3044;
      v_10215 <- load v_10214 16;
      v_10221 <- getRegister v_3045;
      setRegister (lhs.of_reg v_3045) (concat (mux (eq (extract v_10211 6 7) (expression.bv_nat 1 1)) (extract v_10215 0 64) (extract v_10215 64 128)) (mux (eq (extract v_10211 7 8) (expression.bv_nat 1 1)) (extract v_10221 0 64) (extract v_10221 64 128)));
      pure ()
    pat_end
