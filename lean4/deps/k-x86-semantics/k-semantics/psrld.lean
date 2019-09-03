def psrld1 : instruction :=
  definst "psrld" $ do
    pattern fun (v_3031 : imm int) (v_3030 : reg (bv 128)) => do
      v_8130 <- eval (handleImmediateWithSignExtend v_3031 8 8);
      v_8133 <- getRegister v_3030;
      v_8136 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_8130));
      setRegister (lhs.of_reg v_3030) (mux (ugt (concat (expression.bv_nat 56 0) v_8130) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8133 0 32) v_8136) (concat (lshr (extract v_8133 32 64) v_8136) (concat (lshr (extract v_8133 64 96) v_8136) (lshr (extract v_8133 96 128) v_8136)))));
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 128)) (v_3040 : reg (bv 128)) => do
      v_8153 <- getRegister v_3039;
      v_8156 <- getRegister v_3040;
      v_8159 <- eval (uvalueMInt (extract v_8153 96 128));
      setRegister (lhs.of_reg v_3040) (mux (ugt (extract v_8153 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_8156 0 32) v_8159) (concat (lshr (extract v_8156 32 64) v_8159) (concat (lshr (extract v_8156 64 96) v_8159) (lshr (extract v_8156 96 128) v_8159)))));
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) (v_3035 : reg (bv 128)) => do
      v_15133 <- evaluateAddress v_3034;
      v_15134 <- load v_15133 16;
      v_15137 <- getRegister v_3035;
      v_15140 <- eval (uvalueMInt (extract v_15134 96 128));
      setRegister (lhs.of_reg v_3035) (mux (ugt (extract v_15134 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_15137 0 32) v_15140) (concat (lshr (extract v_15137 32 64) v_15140) (concat (lshr (extract v_15137 64 96) v_15140) (lshr (extract v_15137 96 128) v_15140)))));
      pure ()
    pat_end
