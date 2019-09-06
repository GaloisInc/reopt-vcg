def unpckhpd1 : instruction :=
  definst "unpckhpd" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) => do
      v_4763 <- getRegister v_2624;
      v_4765 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2625) (concat (extract v_4763 0 64) (extract v_4765 0 64));
      pure ()
    pat_end;
    pattern fun (v_2617 : Mem) (v_2620 : reg (bv 128)) => do
      v_9085 <- evaluateAddress v_2617;
      v_9086 <- load v_9085 16;
      v_9088 <- getRegister v_2620;
      setRegister (lhs.of_reg v_2620) (concat (extract v_9086 0 64) (extract v_9088 0 64));
      pure ()
    pat_end
