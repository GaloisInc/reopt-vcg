def movzbl1 : instruction :=
  definst "movzbl" $ do
    pattern fun (v_2668 : reg (bv 8)) (v_2667 : reg (bv 32)) => do
      v_4073 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2667) (concat (expression.bv_nat 24 0) v_4073);
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2664 : reg (bv 32)) => do
      v_8874 <- evaluateAddress v_2663;
      v_8875 <- load v_8874 1;
      setRegister (lhs.of_reg v_2664) (concat (expression.bv_nat 24 0) v_8875);
      pure ()
    pat_end
