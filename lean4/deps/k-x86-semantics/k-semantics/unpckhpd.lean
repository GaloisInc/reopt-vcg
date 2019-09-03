def unpckhpd1 : instruction :=
  definst "unpckhpd" $ do
    pattern fun (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_4764 <- getRegister v_2533;
      v_4766 <- getRegister v_2534;
      setRegister (lhs.of_reg v_2534) (concat (extract v_4764 0 64) (extract v_4766 0 64));
      pure ()
    pat_end;
    pattern fun (v_2526 : Mem) (v_2529 : reg (bv 128)) => do
      v_9246 <- evaluateAddress v_2526;
      v_9247 <- load v_9246 16;
      v_9249 <- getRegister v_2529;
      setRegister (lhs.of_reg v_2529) (concat (extract v_9247 0 64) (extract v_9249 0 64));
      pure ()
    pat_end
