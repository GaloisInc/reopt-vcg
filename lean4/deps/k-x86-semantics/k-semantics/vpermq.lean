def vpermq1 : instruction :=
  definst "vpermq" $ do
    pattern fun (v_3146 : imm int) (v_3147 : reg (bv 256)) (v_3148 : reg (bv 256)) => do
      v_8550 <- getRegister v_3147;
      v_8551 <- eval (handleImmediateWithSignExtend v_3146 8 8);
      setRegister (lhs.of_reg v_3148) (concat (extract (lshr v_8550 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8551 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8550 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8551 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_8550 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8551 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_8550 (extract (shl (concat (expression.bv_nat 254 0) (extract v_8551 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3141 : imm int) (v_3142 : Mem) (v_3143 : reg (bv 256)) => do
      v_17048 <- evaluateAddress v_3142;
      v_17049 <- load v_17048 32;
      v_17050 <- eval (handleImmediateWithSignExtend v_3141 8 8);
      setRegister (lhs.of_reg v_3143) (concat (extract (lshr v_17049 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17050 0 2)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_17049 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17050 2 4)) (expression.bv_nat 256 6)) 0 256)) 192 256) (concat (extract (lshr v_17049 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17050 4 6)) (expression.bv_nat 256 6)) 0 256)) 192 256) (extract (lshr v_17049 (extract (shl (concat (expression.bv_nat 254 0) (extract v_17050 6 8)) (expression.bv_nat 256 6)) 0 256)) 192 256))));
      pure ()
    pat_end
