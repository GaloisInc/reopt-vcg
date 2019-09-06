def vpand1 : instruction :=
  definst "vpand" $ do
    pattern fun (v_2607 : Mem) (v_2608 : reg (bv 128)) (v_2609 : reg (bv 128)) => do
      v_14446 <- getRegister v_2608;
      v_14447 <- evaluateAddress v_2607;
      v_14448 <- load v_14447 16;
      setRegister (lhs.of_reg v_2609) (bv_and v_14446 v_14448);
      pure ()
    pat_end;
    pattern fun (v_2618 : Mem) (v_2619 : reg (bv 256)) (v_2620 : reg (bv 256)) => do
      v_14451 <- getRegister v_2619;
      v_14452 <- evaluateAddress v_2618;
      v_14453 <- load v_14452 32;
      setRegister (lhs.of_reg v_2620) (bv_and v_14451 v_14453);
      pure ()
    pat_end
