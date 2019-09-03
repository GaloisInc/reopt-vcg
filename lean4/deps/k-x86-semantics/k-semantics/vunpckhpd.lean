def vunpckhpd1 : instruction :=
  definst "vunpckhpd" $ do
    pattern fun (v_2481 : reg (bv 128)) (v_2482 : reg (bv 128)) (v_2483 : reg (bv 128)) => do
      v_3681 <- getRegister v_2481;
      v_3683 <- getRegister v_2482;
      setRegister (lhs.of_reg v_2483) (concat (extract v_3681 0 64) (extract v_3683 0 64));
      pure ()
    pat_end;
    pattern fun (v_2493 : reg (bv 256)) (v_2494 : reg (bv 256)) (v_2495 : reg (bv 256)) => do
      v_3692 <- getRegister v_2493;
      v_3694 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2495) (concat (concat (extract v_3692 0 64) (extract v_3694 0 64)) (concat (extract v_3692 128 192) (extract v_3694 128 192)));
      pure ()
    pat_end;
    pattern fun (v_2476 : Mem) (v_2477 : reg (bv 128)) (v_2478 : reg (bv 128)) => do
      v_6932 <- evaluateAddress v_2476;
      v_6933 <- load v_6932 16;
      v_6935 <- getRegister v_2477;
      setRegister (lhs.of_reg v_2478) (concat (extract v_6933 0 64) (extract v_6935 0 64));
      pure ()
    pat_end;
    pattern fun (v_2487 : Mem) (v_2488 : reg (bv 256)) (v_2489 : reg (bv 256)) => do
      v_6939 <- evaluateAddress v_2487;
      v_6940 <- load v_6939 32;
      v_6942 <- getRegister v_2488;
      setRegister (lhs.of_reg v_2489) (concat (concat (extract v_6940 0 64) (extract v_6942 0 64)) (concat (extract v_6940 128 192) (extract v_6942 128 192)));
      pure ()
    pat_end
