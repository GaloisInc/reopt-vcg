def unpcklpd1 : instruction :=
  definst "unpcklpd" $ do
    pattern fun (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_4760 <- getRegister v_2615;
      v_4762 <- getRegister v_2616;
      setRegister (lhs.of_reg v_2616) (concat (extract v_4760 64 128) (extract v_4762 64 128));
      pure ()
    pat_end;
    pattern fun (v_2610 : Mem) (v_2611 : reg (bv 128)) => do
      v_9076 <- evaluateAddress v_2610;
      v_9077 <- load v_9076 16;
      v_9079 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2611) (concat (extract v_9077 64 128) (extract v_9079 64 128));
      pure ()
    pat_end
