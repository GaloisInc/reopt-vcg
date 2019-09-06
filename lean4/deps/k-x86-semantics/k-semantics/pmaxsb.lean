def pmaxsb1 : instruction :=
  definst "pmaxsb" $ do
    pattern fun (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) => do
      v_4759 <- getRegister v_2640;
      v_4760 <- eval (extract v_4759 0 8);
      v_4761 <- getRegister v_2639;
      v_4762 <- eval (extract v_4761 0 8);
      v_4765 <- eval (extract v_4759 8 16);
      v_4766 <- eval (extract v_4761 8 16);
      v_4769 <- eval (extract v_4759 16 24);
      v_4770 <- eval (extract v_4761 16 24);
      v_4773 <- eval (extract v_4759 24 32);
      v_4774 <- eval (extract v_4761 24 32);
      v_4777 <- eval (extract v_4759 32 40);
      v_4778 <- eval (extract v_4761 32 40);
      v_4781 <- eval (extract v_4759 40 48);
      v_4782 <- eval (extract v_4761 40 48);
      v_4785 <- eval (extract v_4759 48 56);
      v_4786 <- eval (extract v_4761 48 56);
      v_4789 <- eval (extract v_4759 56 64);
      v_4790 <- eval (extract v_4761 56 64);
      v_4793 <- eval (extract v_4759 64 72);
      v_4794 <- eval (extract v_4761 64 72);
      v_4797 <- eval (extract v_4759 72 80);
      v_4798 <- eval (extract v_4761 72 80);
      v_4801 <- eval (extract v_4759 80 88);
      v_4802 <- eval (extract v_4761 80 88);
      v_4805 <- eval (extract v_4759 88 96);
      v_4806 <- eval (extract v_4761 88 96);
      v_4809 <- eval (extract v_4759 96 104);
      v_4810 <- eval (extract v_4761 96 104);
      v_4813 <- eval (extract v_4759 104 112);
      v_4814 <- eval (extract v_4761 104 112);
      v_4817 <- eval (extract v_4759 112 120);
      v_4818 <- eval (extract v_4761 112 120);
      v_4821 <- eval (extract v_4759 120 128);
      v_4822 <- eval (extract v_4761 120 128);
      setRegister (lhs.of_reg v_2640) (concat (mux (sgt v_4760 v_4762) v_4760 v_4762) (concat (mux (sgt v_4765 v_4766) v_4765 v_4766) (concat (mux (sgt v_4769 v_4770) v_4769 v_4770) (concat (mux (sgt v_4773 v_4774) v_4773 v_4774) (concat (mux (sgt v_4777 v_4778) v_4777 v_4778) (concat (mux (sgt v_4781 v_4782) v_4781 v_4782) (concat (mux (sgt v_4785 v_4786) v_4785 v_4786) (concat (mux (sgt v_4789 v_4790) v_4789 v_4790) (concat (mux (sgt v_4793 v_4794) v_4793 v_4794) (concat (mux (sgt v_4797 v_4798) v_4797 v_4798) (concat (mux (sgt v_4801 v_4802) v_4801 v_4802) (concat (mux (sgt v_4805 v_4806) v_4805 v_4806) (concat (mux (sgt v_4809 v_4810) v_4809 v_4810) (concat (mux (sgt v_4813 v_4814) v_4813 v_4814) (concat (mux (sgt v_4817 v_4818) v_4817 v_4818) (mux (sgt v_4821 v_4822) v_4821 v_4822))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2635 : Mem) (v_2636 : reg (bv 128)) => do
      v_11612 <- getRegister v_2636;
      v_11613 <- eval (extract v_11612 0 8);
      v_11614 <- evaluateAddress v_2635;
      v_11615 <- load v_11614 16;
      v_11616 <- eval (extract v_11615 0 8);
      v_11619 <- eval (extract v_11612 8 16);
      v_11620 <- eval (extract v_11615 8 16);
      v_11623 <- eval (extract v_11612 16 24);
      v_11624 <- eval (extract v_11615 16 24);
      v_11627 <- eval (extract v_11612 24 32);
      v_11628 <- eval (extract v_11615 24 32);
      v_11631 <- eval (extract v_11612 32 40);
      v_11632 <- eval (extract v_11615 32 40);
      v_11635 <- eval (extract v_11612 40 48);
      v_11636 <- eval (extract v_11615 40 48);
      v_11639 <- eval (extract v_11612 48 56);
      v_11640 <- eval (extract v_11615 48 56);
      v_11643 <- eval (extract v_11612 56 64);
      v_11644 <- eval (extract v_11615 56 64);
      v_11647 <- eval (extract v_11612 64 72);
      v_11648 <- eval (extract v_11615 64 72);
      v_11651 <- eval (extract v_11612 72 80);
      v_11652 <- eval (extract v_11615 72 80);
      v_11655 <- eval (extract v_11612 80 88);
      v_11656 <- eval (extract v_11615 80 88);
      v_11659 <- eval (extract v_11612 88 96);
      v_11660 <- eval (extract v_11615 88 96);
      v_11663 <- eval (extract v_11612 96 104);
      v_11664 <- eval (extract v_11615 96 104);
      v_11667 <- eval (extract v_11612 104 112);
      v_11668 <- eval (extract v_11615 104 112);
      v_11671 <- eval (extract v_11612 112 120);
      v_11672 <- eval (extract v_11615 112 120);
      v_11675 <- eval (extract v_11612 120 128);
      v_11676 <- eval (extract v_11615 120 128);
      setRegister (lhs.of_reg v_2636) (concat (mux (sgt v_11613 v_11616) v_11613 v_11616) (concat (mux (sgt v_11619 v_11620) v_11619 v_11620) (concat (mux (sgt v_11623 v_11624) v_11623 v_11624) (concat (mux (sgt v_11627 v_11628) v_11627 v_11628) (concat (mux (sgt v_11631 v_11632) v_11631 v_11632) (concat (mux (sgt v_11635 v_11636) v_11635 v_11636) (concat (mux (sgt v_11639 v_11640) v_11639 v_11640) (concat (mux (sgt v_11643 v_11644) v_11643 v_11644) (concat (mux (sgt v_11647 v_11648) v_11647 v_11648) (concat (mux (sgt v_11651 v_11652) v_11651 v_11652) (concat (mux (sgt v_11655 v_11656) v_11655 v_11656) (concat (mux (sgt v_11659 v_11660) v_11659 v_11660) (concat (mux (sgt v_11663 v_11664) v_11663 v_11664) (concat (mux (sgt v_11667 v_11668) v_11667 v_11668) (concat (mux (sgt v_11671 v_11672) v_11671 v_11672) (mux (sgt v_11675 v_11676) v_11675 v_11676))))))))))))))));
      pure ()
    pat_end
