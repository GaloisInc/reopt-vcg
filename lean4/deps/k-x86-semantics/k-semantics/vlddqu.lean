def vlddqu1 : instruction :=
  definst "vlddqu" $ do
    pattern fun (v_2498 : Mem) (v_2499 : reg (bv 128)) => do
      v_10671 <- evaluateAddress v_2498;
      v_10672 <- load v_10671 16;
      setRegister (lhs.of_reg v_2499) v_10672;
      pure ()
    pat_end;
    pattern fun (v_2502 : Mem) (v_2503 : reg (bv 256)) => do
      v_10674 <- evaluateAddress v_2502;
      v_10675 <- load v_10674 32;
      setRegister (lhs.of_reg v_2503) v_10675;
      pure ()
    pat_end
