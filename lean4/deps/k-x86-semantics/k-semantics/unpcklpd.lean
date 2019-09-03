def unpcklpd1 : instruction :=
  definst "unpcklpd" $ do
    pattern fun (v_2564 : reg (bv 128)) (v_2565 : reg (bv 128)) => do
      v_4799 <- getRegister v_2564;
      v_4801 <- getRegister v_2565;
      setRegister (lhs.of_reg v_2565) (concat (extract v_4799 64 128) (extract v_4801 64 128));
      pure ()
    pat_end;
    pattern fun (v_2557 : Mem) (v_2560 : reg (bv 128)) => do
      v_10358 <- evaluateAddress v_2557;
      v_10359 <- load v_10358 16;
      v_10361 <- getRegister v_2560;
      setRegister (lhs.of_reg v_2560) (concat (extract v_10359 64 128) (extract v_10361 64 128));
      pure ()
    pat_end
