def vxorpd1 : instruction :=
  definst "vxorpd" $ do
    pattern fun (v_2564 : Mem) (v_2565 : reg (bv 128)) (v_2566 : reg (bv 128)) => do
      v_7028 <- getRegister v_2565;
      v_7029 <- evaluateAddress v_2564;
      v_7030 <- load v_7029 16;
      setRegister (lhs.of_reg v_2566) (bv_xor v_7028 v_7030);
      pure ()
    pat_end;
    pattern fun (v_2575 : Mem) (v_2576 : reg (bv 256)) (v_2577 : reg (bv 256)) => do
      v_7033 <- getRegister v_2576;
      v_7034 <- evaluateAddress v_2575;
      v_7035 <- load v_7034 32;
      setRegister (lhs.of_reg v_2577) (bv_xor v_7033 v_7035);
      pure ()
    pat_end
