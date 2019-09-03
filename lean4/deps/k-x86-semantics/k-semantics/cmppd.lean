def cmppd1 : instruction :=
  definst "cmppd" $ do
    pattern fun (v_3385 : imm int) (v_3387 : reg (bv 128)) (v_3388 : reg (bv 128)) => do
      v_5642 <- getRegister v_3388;
      v_5644 <- getRegister v_3387;
      v_5646 <- eval (handleImmediateWithSignExtend v_3385 8 8);
      setRegister (lhs.of_reg v_3388) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5642 0 64) (extract v_5644 0 64) v_5646) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_5642 64 128) (extract v_5644 64 128) v_5646) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3380 : imm int) (v_3381 : Mem) (v_3382 : reg (bv 128)) => do
      v_8977 <- getRegister v_3382;
      v_8979 <- evaluateAddress v_3381;
      v_8980 <- load v_8979 16;
      v_8982 <- eval (handleImmediateWithSignExtend v_3380 8 8);
      setRegister (lhs.of_reg v_3382) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8977 0 64) (extract v_8980 0 64) v_8982) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_double_pred (extract v_8977 64 128) (extract v_8980 64 128) v_8982) (expression.bv_nat 1 1)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
