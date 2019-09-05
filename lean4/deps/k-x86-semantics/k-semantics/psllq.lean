def psllq1 : instruction :=
  definst "psllq" $ do
    pattern fun (v_3038 : imm int) (v_3037 : reg (bv 128)) => do
      v_7590 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3038 8 8));
      v_7592 <- getRegister v_3037;
      setRegister (lhs.of_reg v_3037) (mux (ugt v_7590 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7592 0 64) v_7590) 0 64) (extract (shl (extract v_7592 64 128) v_7590) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3046 : reg (bv 128)) (v_3047 : reg (bv 128)) => do
      v_7606 <- getRegister v_3046;
      v_7607 <- eval (extract v_7606 64 128);
      v_7609 <- getRegister v_3047;
      setRegister (lhs.of_reg v_3047) (mux (ugt v_7607 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7609 0 64) v_7607) 0 64) (extract (shl (extract v_7609 64 128) v_7607) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3043 : Mem) (v_3042 : reg (bv 128)) => do
      v_14262 <- evaluateAddress v_3043;
      v_14263 <- load v_14262 16;
      v_14264 <- eval (extract v_14263 64 128);
      v_14266 <- getRegister v_3042;
      setRegister (lhs.of_reg v_3042) (mux (ugt v_14264 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14266 0 64) v_14264) 0 64) (extract (shl (extract v_14266 64 128) v_14264) 0 64)));
      pure ()
    pat_end
