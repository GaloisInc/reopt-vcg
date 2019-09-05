def vpbroadcastd1 : instruction :=
  definst "vpbroadcastd" $ do
    pattern fun (v_2769 : reg (bv 128)) (v_2770 : reg (bv 128)) => do
      v_6948 <- getRegister v_2769;
      v_6949 <- eval (extract v_6948 96 128);
      setRegister (lhs.of_reg v_2770) (concat (concat (concat v_6949 v_6949) v_6949) v_6949);
      pure ()
    pat_end;
    pattern fun (v_2779 : reg (bv 128)) (v_2777 : reg (bv 256)) => do
      v_6958 <- getRegister v_2779;
      v_6959 <- eval (extract v_6958 96 128);
      setRegister (lhs.of_reg v_2777) (concat (concat (concat (concat v_6959 v_6959) v_6959) v_6959) (concat (concat (concat v_6959 v_6959) v_6959) v_6959));
      pure ()
    pat_end;
    pattern fun (v_2764 : Mem) (v_2765 : reg (bv 128)) => do
      v_15589 <- evaluateAddress v_2764;
      v_15590 <- load v_15589 4;
      setRegister (lhs.of_reg v_2765) (concat (concat (concat v_15590 v_15590) v_15590) v_15590);
      pure ()
    pat_end;
    pattern fun (v_2773 : Mem) (v_2774 : reg (bv 256)) => do
      v_15595 <- evaluateAddress v_2773;
      v_15596 <- load v_15595 4;
      setRegister (lhs.of_reg v_2774) (concat (concat (concat (concat v_15596 v_15596) v_15596) v_15596) (concat (concat (concat v_15596 v_15596) v_15596) v_15596));
      pure ()
    pat_end
