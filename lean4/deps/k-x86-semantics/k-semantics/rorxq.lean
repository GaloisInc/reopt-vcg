def rorxq1 : instruction :=
  definst "rorxq" $ do
    pattern fun (v_2889 : imm int) (v_2887 : reg (bv 64)) (v_2888 : reg (bv 64)) => do
      v_5190 <- getRegister v_2887;
      v_5193 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2889 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2888) (bv_or (lshr v_5190 v_5193) (extract (shl v_5190 (sub (expression.bv_nat 64 64) v_5193)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2878 : imm int) (v_2879 : Mem) (v_2877 : reg (bv 64)) => do
      v_10504 <- evaluateAddress v_2879;
      v_10505 <- load v_10504 8;
      v_10508 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2878 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2877) (bv_or (lshr v_10505 v_10508) (extract (shl v_10505 (sub (expression.bv_nat 64 64) v_10508)) 0 64));
      pure ()
    pat_end
