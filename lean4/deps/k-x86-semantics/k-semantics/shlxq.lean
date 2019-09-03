def shlxq1 : instruction :=
  definst "shlxq" $ do
    pattern fun (v_2863 : reg (bv 64)) (v_2864 : reg (bv 64)) (v_2865 : reg (bv 64)) => do
      v_5467 <- getRegister v_2864;
      v_5468 <- getRegister v_2863;
      setRegister (lhs.of_reg v_2865) (extract (shl v_5467 (uvalueMInt (bv_and v_5468 (expression.bv_nat 64 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2854 : reg (bv 64)) (v_2853 : Mem) (v_2855 : reg (bv 64)) => do
      v_10111 <- evaluateAddress v_2853;
      v_10112 <- load v_10111 8;
      v_10113 <- getRegister v_2854;
      setRegister (lhs.of_reg v_2855) (extract (shl v_10112 (uvalueMInt (bv_and v_10113 (expression.bv_nat 64 63)))) 0 64);
      pure ()
    pat_end
