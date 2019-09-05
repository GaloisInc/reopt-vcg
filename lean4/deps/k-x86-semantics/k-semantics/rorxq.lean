def rorxq1 : instruction :=
  definst "rorxq" $ do
    pattern fun (v_2862 : imm int) (v_2864 : reg (bv 64)) (v_2865 : reg (bv 64)) => do
      v_5482 <- getRegister v_2864;
      v_5485 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2862 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2865) (bv_or (lshr v_5482 v_5485) (extract (shl v_5482 (sub (expression.bv_nat 64 64) v_5485)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2852 : imm int) (v_2853 : Mem) (v_2854 : reg (bv 64)) => do
      v_11248 <- evaluateAddress v_2853;
      v_11249 <- load v_11248 8;
      v_11252 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2852 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2854) (bv_or (lshr v_11249 v_11252) (extract (shl v_11249 (sub (expression.bv_nat 64 64) v_11252)) 0 64));
      pure ()
    pat_end
