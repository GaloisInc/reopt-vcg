def psrld1 : instruction :=
  definst "psrld" $ do
    pattern fun (v_3121 : imm int) (v_3122 : reg (bv 128)) => do
      v_7830 <- eval (handleImmediateWithSignExtend v_3121 8 8);
      v_7833 <- getRegister v_3122;
      v_7835 <- eval (concat (expression.bv_nat 24 0) v_7830);
      setRegister (lhs.of_reg v_3122) (mux (ugt (concat (expression.bv_nat 56 0) v_7830) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7833 0 32) v_7835) (concat (lshr (extract v_7833 32 64) v_7835) (concat (lshr (extract v_7833 64 96) v_7835) (lshr (extract v_7833 96 128) v_7835)))));
      pure ()
    pat_end;
    pattern fun (v_3130 : reg (bv 128)) (v_3131 : reg (bv 128)) => do
      v_7852 <- getRegister v_3130;
      v_7855 <- getRegister v_3131;
      v_7857 <- eval (extract v_7852 96 128);
      setRegister (lhs.of_reg v_3131) (mux (ugt (extract v_7852 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7855 0 32) v_7857) (concat (lshr (extract v_7855 32 64) v_7857) (concat (lshr (extract v_7855 64 96) v_7857) (lshr (extract v_7855 96 128) v_7857)))));
      pure ()
    pat_end;
    pattern fun (v_3126 : Mem) (v_3127 : reg (bv 128)) => do
      v_14341 <- evaluateAddress v_3126;
      v_14342 <- load v_14341 16;
      v_14345 <- getRegister v_3127;
      v_14347 <- eval (extract v_14342 96 128);
      setRegister (lhs.of_reg v_3127) (mux (ugt (extract v_14342 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14345 0 32) v_14347) (concat (lshr (extract v_14345 32 64) v_14347) (concat (lshr (extract v_14345 64 96) v_14347) (lshr (extract v_14345 96 128) v_14347)))));
      pure ()
    pat_end
