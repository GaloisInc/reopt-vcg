def vpminsw1 : instruction :=
  definst "vpminsw" $ do
    pattern fun (v_2560 : reg (bv 128)) (v_2561 : reg (bv 128)) (v_2562 : reg (bv 128)) => do
      v_4761 <- getRegister v_2561;
      v_4762 <- eval (extract v_4761 0 16);
      v_4763 <- getRegister v_2560;
      v_4764 <- eval (extract v_4763 0 16);
      v_4767 <- eval (extract v_4761 16 32);
      v_4768 <- eval (extract v_4763 16 32);
      v_4771 <- eval (extract v_4761 32 48);
      v_4772 <- eval (extract v_4763 32 48);
      v_4775 <- eval (extract v_4761 48 64);
      v_4776 <- eval (extract v_4763 48 64);
      v_4779 <- eval (extract v_4761 64 80);
      v_4780 <- eval (extract v_4763 64 80);
      v_4783 <- eval (extract v_4761 80 96);
      v_4784 <- eval (extract v_4763 80 96);
      v_4787 <- eval (extract v_4761 96 112);
      v_4788 <- eval (extract v_4763 96 112);
      v_4791 <- eval (extract v_4761 112 128);
      v_4792 <- eval (extract v_4763 112 128);
      setRegister (lhs.of_reg v_2562) (concat (mux (slt v_4762 v_4764) v_4762 v_4764) (concat (mux (slt v_4767 v_4768) v_4767 v_4768) (concat (mux (slt v_4771 v_4772) v_4771 v_4772) (concat (mux (slt v_4775 v_4776) v_4775 v_4776) (concat (mux (slt v_4779 v_4780) v_4779 v_4780) (concat (mux (slt v_4783 v_4784) v_4783 v_4784) (concat (mux (slt v_4787 v_4788) v_4787 v_4788) (mux (slt v_4791 v_4792) v_4791 v_4792))))))));
      pure ()
    pat_end;
    pattern fun (v_2554 : Mem) (v_2555 : reg (bv 128)) (v_2556 : reg (bv 128)) => do
      v_11418 <- getRegister v_2555;
      v_11419 <- eval (extract v_11418 0 16);
      v_11420 <- evaluateAddress v_2554;
      v_11421 <- load v_11420 16;
      v_11422 <- eval (extract v_11421 0 16);
      v_11425 <- eval (extract v_11418 16 32);
      v_11426 <- eval (extract v_11421 16 32);
      v_11429 <- eval (extract v_11418 32 48);
      v_11430 <- eval (extract v_11421 32 48);
      v_11433 <- eval (extract v_11418 48 64);
      v_11434 <- eval (extract v_11421 48 64);
      v_11437 <- eval (extract v_11418 64 80);
      v_11438 <- eval (extract v_11421 64 80);
      v_11441 <- eval (extract v_11418 80 96);
      v_11442 <- eval (extract v_11421 80 96);
      v_11445 <- eval (extract v_11418 96 112);
      v_11446 <- eval (extract v_11421 96 112);
      v_11449 <- eval (extract v_11418 112 128);
      v_11450 <- eval (extract v_11421 112 128);
      setRegister (lhs.of_reg v_2556) (concat (mux (slt v_11419 v_11422) v_11419 v_11422) (concat (mux (slt v_11425 v_11426) v_11425 v_11426) (concat (mux (slt v_11429 v_11430) v_11429 v_11430) (concat (mux (slt v_11433 v_11434) v_11433 v_11434) (concat (mux (slt v_11437 v_11438) v_11437 v_11438) (concat (mux (slt v_11441 v_11442) v_11441 v_11442) (concat (mux (slt v_11445 v_11446) v_11445 v_11446) (mux (slt v_11449 v_11450) v_11449 v_11450))))))));
      pure ()
    pat_end
