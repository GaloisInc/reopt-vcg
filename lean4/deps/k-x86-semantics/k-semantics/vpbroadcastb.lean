def vpbroadcastb1 : instruction :=
  definst "vpbroadcastb" $ do
    pattern fun (v_2777 : reg (bv 128)) (v_2778 : reg (bv 128)) => do
      v_6915 <- getRegister v_2777;
      v_6916 <- eval (extract v_6915 120 128);
      setRegister (lhs.of_reg v_2778) (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 (concat v_6916 v_6916)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2787 : reg (bv 128)) (v_2786 : reg (bv 256)) => do
      v_6937 <- getRegister v_2787;
      v_6938 <- eval (extract v_6937 120 128);
      setRegister (lhs.of_reg v_2786) (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 (concat v_6938 v_6938)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2773 : Mem) (v_2774 : reg (bv 128)) => do
      v_15564 <- evaluateAddress v_2773;
      v_15565 <- load v_15564 1;
      setRegister (lhs.of_reg v_2774) (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 (concat v_15565 v_15565)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2782 : Mem) (v_2783 : reg (bv 256)) => do
      v_15582 <- evaluateAddress v_2782;
      v_15583 <- load v_15582 1;
      setRegister (lhs.of_reg v_2783) (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 (concat v_15583 v_15583)))))))))))))))))))))))))))))));
      pure ()
    pat_end
