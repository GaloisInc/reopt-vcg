def pmaxsb1 : instruction :=
  definst "pmaxsb" $ do
    pattern fun (v_2611 : reg (bv 128)) (v_2612 : reg (bv 128)) => do
      v_4732 <- getRegister v_2612;
      v_4733 <- eval (extract v_4732 0 8);
      v_4734 <- getRegister v_2611;
      v_4735 <- eval (extract v_4734 0 8);
      v_4738 <- eval (extract v_4732 8 16);
      v_4739 <- eval (extract v_4734 8 16);
      v_4742 <- eval (extract v_4732 16 24);
      v_4743 <- eval (extract v_4734 16 24);
      v_4746 <- eval (extract v_4732 24 32);
      v_4747 <- eval (extract v_4734 24 32);
      v_4750 <- eval (extract v_4732 32 40);
      v_4751 <- eval (extract v_4734 32 40);
      v_4754 <- eval (extract v_4732 40 48);
      v_4755 <- eval (extract v_4734 40 48);
      v_4758 <- eval (extract v_4732 48 56);
      v_4759 <- eval (extract v_4734 48 56);
      v_4762 <- eval (extract v_4732 56 64);
      v_4763 <- eval (extract v_4734 56 64);
      v_4766 <- eval (extract v_4732 64 72);
      v_4767 <- eval (extract v_4734 64 72);
      v_4770 <- eval (extract v_4732 72 80);
      v_4771 <- eval (extract v_4734 72 80);
      v_4774 <- eval (extract v_4732 80 88);
      v_4775 <- eval (extract v_4734 80 88);
      v_4778 <- eval (extract v_4732 88 96);
      v_4779 <- eval (extract v_4734 88 96);
      v_4782 <- eval (extract v_4732 96 104);
      v_4783 <- eval (extract v_4734 96 104);
      v_4786 <- eval (extract v_4732 104 112);
      v_4787 <- eval (extract v_4734 104 112);
      v_4790 <- eval (extract v_4732 112 120);
      v_4791 <- eval (extract v_4734 112 120);
      v_4794 <- eval (extract v_4732 120 128);
      v_4795 <- eval (extract v_4734 120 128);
      setRegister (lhs.of_reg v_2612) (concat (mux (sgt v_4733 v_4735) v_4733 v_4735) (concat (mux (sgt v_4738 v_4739) v_4738 v_4739) (concat (mux (sgt v_4742 v_4743) v_4742 v_4743) (concat (mux (sgt v_4746 v_4747) v_4746 v_4747) (concat (mux (sgt v_4750 v_4751) v_4750 v_4751) (concat (mux (sgt v_4754 v_4755) v_4754 v_4755) (concat (mux (sgt v_4758 v_4759) v_4758 v_4759) (concat (mux (sgt v_4762 v_4763) v_4762 v_4763) (concat (mux (sgt v_4766 v_4767) v_4766 v_4767) (concat (mux (sgt v_4770 v_4771) v_4770 v_4771) (concat (mux (sgt v_4774 v_4775) v_4774 v_4775) (concat (mux (sgt v_4778 v_4779) v_4778 v_4779) (concat (mux (sgt v_4782 v_4783) v_4782 v_4783) (concat (mux (sgt v_4786 v_4787) v_4786 v_4787) (concat (mux (sgt v_4790 v_4791) v_4790 v_4791) (mux (sgt v_4794 v_4795) v_4794 v_4795))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2608 : Mem) (v_2607 : reg (bv 128)) => do
      v_11636 <- getRegister v_2607;
      v_11637 <- eval (extract v_11636 0 8);
      v_11638 <- evaluateAddress v_2608;
      v_11639 <- load v_11638 16;
      v_11640 <- eval (extract v_11639 0 8);
      v_11643 <- eval (extract v_11636 8 16);
      v_11644 <- eval (extract v_11639 8 16);
      v_11647 <- eval (extract v_11636 16 24);
      v_11648 <- eval (extract v_11639 16 24);
      v_11651 <- eval (extract v_11636 24 32);
      v_11652 <- eval (extract v_11639 24 32);
      v_11655 <- eval (extract v_11636 32 40);
      v_11656 <- eval (extract v_11639 32 40);
      v_11659 <- eval (extract v_11636 40 48);
      v_11660 <- eval (extract v_11639 40 48);
      v_11663 <- eval (extract v_11636 48 56);
      v_11664 <- eval (extract v_11639 48 56);
      v_11667 <- eval (extract v_11636 56 64);
      v_11668 <- eval (extract v_11639 56 64);
      v_11671 <- eval (extract v_11636 64 72);
      v_11672 <- eval (extract v_11639 64 72);
      v_11675 <- eval (extract v_11636 72 80);
      v_11676 <- eval (extract v_11639 72 80);
      v_11679 <- eval (extract v_11636 80 88);
      v_11680 <- eval (extract v_11639 80 88);
      v_11683 <- eval (extract v_11636 88 96);
      v_11684 <- eval (extract v_11639 88 96);
      v_11687 <- eval (extract v_11636 96 104);
      v_11688 <- eval (extract v_11639 96 104);
      v_11691 <- eval (extract v_11636 104 112);
      v_11692 <- eval (extract v_11639 104 112);
      v_11695 <- eval (extract v_11636 112 120);
      v_11696 <- eval (extract v_11639 112 120);
      v_11699 <- eval (extract v_11636 120 128);
      v_11700 <- eval (extract v_11639 120 128);
      setRegister (lhs.of_reg v_2607) (concat (mux (sgt v_11637 v_11640) v_11637 v_11640) (concat (mux (sgt v_11643 v_11644) v_11643 v_11644) (concat (mux (sgt v_11647 v_11648) v_11647 v_11648) (concat (mux (sgt v_11651 v_11652) v_11651 v_11652) (concat (mux (sgt v_11655 v_11656) v_11655 v_11656) (concat (mux (sgt v_11659 v_11660) v_11659 v_11660) (concat (mux (sgt v_11663 v_11664) v_11663 v_11664) (concat (mux (sgt v_11667 v_11668) v_11667 v_11668) (concat (mux (sgt v_11671 v_11672) v_11671 v_11672) (concat (mux (sgt v_11675 v_11676) v_11675 v_11676) (concat (mux (sgt v_11679 v_11680) v_11679 v_11680) (concat (mux (sgt v_11683 v_11684) v_11683 v_11684) (concat (mux (sgt v_11687 v_11688) v_11687 v_11688) (concat (mux (sgt v_11691 v_11692) v_11691 v_11692) (concat (mux (sgt v_11695 v_11696) v_11695 v_11696) (mux (sgt v_11699 v_11700) v_11699 v_11700))))))))))))))));
      pure ()
    pat_end
