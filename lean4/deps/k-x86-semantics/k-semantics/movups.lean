def movups1 : instruction :=
  definst "movups" $ do
    pattern fun (v_2636 : reg (bv 128)) (v_2637 : reg (bv 128)) => do
      v_4051 <- getRegister v_2636;
      setRegister (lhs.of_reg v_2637) v_4051;
      pure ()
    pat_end;
    pattern fun (v_2629 : reg (bv 128)) (v_2628 : Mem) => do
      v_8627 <- evaluateAddress v_2628;
      v_8628 <- getRegister v_2629;
      store v_8627 v_8628 16;
      pure ()
    pat_end;
    pattern fun (v_2632 : Mem) (v_2633 : reg (bv 128)) => do
      v_8868 <- evaluateAddress v_2632;
      v_8869 <- load v_8868 16;
      setRegister (lhs.of_reg v_2633) v_8869;
      pure ()
    pat_end
