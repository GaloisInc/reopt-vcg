def shrx1 : instruction :=
  definst "shrx" $ do
    pattern fun (v_3090 : reg (bv 32)) (v_3091 : reg (bv 32)) (v_3092 : reg (bv 32)) => do
      v_6654 <- getRegister v_3091;
      v_6655 <- getRegister v_3090;
      setRegister (lhs.of_reg v_3092) (lshr v_6654 (bv_and v_6655 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3111 : reg (bv 64)) (v_3112 : reg (bv 64)) (v_3113 : reg (bv 64)) => do
      v_6670 <- getRegister v_3112;
      v_6672 <- getRegister v_3111;
      setRegister (lhs.of_reg v_3113) (extract (lshr (concat v_6670 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_6672 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3080 : reg (bv 32)) (v_3082 : Mem) (v_3081 : reg (bv 32)) => do
      v_9766 <- evaluateAddress v_3082;
      v_9767 <- load v_9766 4;
      v_9768 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3081) (lshr v_9767 (bv_and v_9768 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 64)) (v_3101 : Mem) (v_3103 : reg (bv 64)) => do
      v_9772 <- evaluateAddress v_3101;
      v_9773 <- load v_9772 8;
      v_9775 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3103) (extract (lshr (concat v_9773 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_9775 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end
