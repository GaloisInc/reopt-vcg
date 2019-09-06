def unpcklpd1 : instruction :=
  definst "unpcklpd" $ do
    pattern fun (v_2642 : reg (bv 128)) (v_2643 : reg (bv 128)) => do
      v_4787 <- getRegister v_2642;
      v_4789 <- getRegister v_2643;
      setRegister (lhs.of_reg v_2643) (concat (extract v_4787 64 128) (extract v_4789 64 128));
      pure ()
    pat_end;
    pattern fun (v_2635 : Mem) (v_2638 : reg (bv 128)) => do
      v_9103 <- evaluateAddress v_2635;
      v_9104 <- load v_9103 16;
      v_9106 <- getRegister v_2638;
      setRegister (lhs.of_reg v_2638) (concat (extract v_9104 64 128) (extract v_9106 64 128));
      pure ()
    pat_end
