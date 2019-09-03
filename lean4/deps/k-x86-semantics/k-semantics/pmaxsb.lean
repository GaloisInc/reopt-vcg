def pmaxsb1 : instruction :=
  definst "pmaxsb" $ do
    pattern fun (v_2562 : reg (bv 128)) (v_2563 : reg (bv 128)) => do
      v_4701 <- getRegister v_2563;
      v_4702 <- eval (extract v_4701 0 8);
      v_4703 <- getRegister v_2562;
      v_4704 <- eval (extract v_4703 0 8);
      v_4707 <- eval (extract v_4701 8 16);
      v_4708 <- eval (extract v_4703 8 16);
      v_4711 <- eval (extract v_4701 16 24);
      v_4712 <- eval (extract v_4703 16 24);
      v_4715 <- eval (extract v_4701 24 32);
      v_4716 <- eval (extract v_4703 24 32);
      v_4719 <- eval (extract v_4701 32 40);
      v_4720 <- eval (extract v_4703 32 40);
      v_4723 <- eval (extract v_4701 40 48);
      v_4724 <- eval (extract v_4703 40 48);
      v_4727 <- eval (extract v_4701 48 56);
      v_4728 <- eval (extract v_4703 48 56);
      v_4731 <- eval (extract v_4701 56 64);
      v_4732 <- eval (extract v_4703 56 64);
      v_4735 <- eval (extract v_4701 64 72);
      v_4736 <- eval (extract v_4703 64 72);
      v_4739 <- eval (extract v_4701 72 80);
      v_4740 <- eval (extract v_4703 72 80);
      v_4743 <- eval (extract v_4701 80 88);
      v_4744 <- eval (extract v_4703 80 88);
      v_4747 <- eval (extract v_4701 88 96);
      v_4748 <- eval (extract v_4703 88 96);
      v_4751 <- eval (extract v_4701 96 104);
      v_4752 <- eval (extract v_4703 96 104);
      v_4755 <- eval (extract v_4701 104 112);
      v_4756 <- eval (extract v_4703 104 112);
      v_4759 <- eval (extract v_4701 112 120);
      v_4760 <- eval (extract v_4703 112 120);
      v_4763 <- eval (extract v_4701 120 128);
      v_4764 <- eval (extract v_4703 120 128);
      setRegister (lhs.of_reg v_2563) (concat (mux (sgt v_4702 v_4704) v_4702 v_4704) (concat (mux (sgt v_4707 v_4708) v_4707 v_4708) (concat (mux (sgt v_4711 v_4712) v_4711 v_4712) (concat (mux (sgt v_4715 v_4716) v_4715 v_4716) (concat (mux (sgt v_4719 v_4720) v_4719 v_4720) (concat (mux (sgt v_4723 v_4724) v_4723 v_4724) (concat (mux (sgt v_4727 v_4728) v_4727 v_4728) (concat (mux (sgt v_4731 v_4732) v_4731 v_4732) (concat (mux (sgt v_4735 v_4736) v_4735 v_4736) (concat (mux (sgt v_4739 v_4740) v_4739 v_4740) (concat (mux (sgt v_4743 v_4744) v_4743 v_4744) (concat (mux (sgt v_4747 v_4748) v_4747 v_4748) (concat (mux (sgt v_4751 v_4752) v_4751 v_4752) (concat (mux (sgt v_4755 v_4756) v_4755 v_4756) (concat (mux (sgt v_4759 v_4760) v_4759 v_4760) (mux (sgt v_4763 v_4764) v_4763 v_4764))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2558 : Mem) (v_2559 : reg (bv 128)) => do
      v_11778 <- getRegister v_2559;
      v_11779 <- eval (extract v_11778 0 8);
      v_11780 <- evaluateAddress v_2558;
      v_11781 <- load v_11780 16;
      v_11782 <- eval (extract v_11781 0 8);
      v_11785 <- eval (extract v_11778 8 16);
      v_11786 <- eval (extract v_11781 8 16);
      v_11789 <- eval (extract v_11778 16 24);
      v_11790 <- eval (extract v_11781 16 24);
      v_11793 <- eval (extract v_11778 24 32);
      v_11794 <- eval (extract v_11781 24 32);
      v_11797 <- eval (extract v_11778 32 40);
      v_11798 <- eval (extract v_11781 32 40);
      v_11801 <- eval (extract v_11778 40 48);
      v_11802 <- eval (extract v_11781 40 48);
      v_11805 <- eval (extract v_11778 48 56);
      v_11806 <- eval (extract v_11781 48 56);
      v_11809 <- eval (extract v_11778 56 64);
      v_11810 <- eval (extract v_11781 56 64);
      v_11813 <- eval (extract v_11778 64 72);
      v_11814 <- eval (extract v_11781 64 72);
      v_11817 <- eval (extract v_11778 72 80);
      v_11818 <- eval (extract v_11781 72 80);
      v_11821 <- eval (extract v_11778 80 88);
      v_11822 <- eval (extract v_11781 80 88);
      v_11825 <- eval (extract v_11778 88 96);
      v_11826 <- eval (extract v_11781 88 96);
      v_11829 <- eval (extract v_11778 96 104);
      v_11830 <- eval (extract v_11781 96 104);
      v_11833 <- eval (extract v_11778 104 112);
      v_11834 <- eval (extract v_11781 104 112);
      v_11837 <- eval (extract v_11778 112 120);
      v_11838 <- eval (extract v_11781 112 120);
      v_11841 <- eval (extract v_11778 120 128);
      v_11842 <- eval (extract v_11781 120 128);
      setRegister (lhs.of_reg v_2559) (concat (mux (sgt v_11779 v_11782) v_11779 v_11782) (concat (mux (sgt v_11785 v_11786) v_11785 v_11786) (concat (mux (sgt v_11789 v_11790) v_11789 v_11790) (concat (mux (sgt v_11793 v_11794) v_11793 v_11794) (concat (mux (sgt v_11797 v_11798) v_11797 v_11798) (concat (mux (sgt v_11801 v_11802) v_11801 v_11802) (concat (mux (sgt v_11805 v_11806) v_11805 v_11806) (concat (mux (sgt v_11809 v_11810) v_11809 v_11810) (concat (mux (sgt v_11813 v_11814) v_11813 v_11814) (concat (mux (sgt v_11817 v_11818) v_11817 v_11818) (concat (mux (sgt v_11821 v_11822) v_11821 v_11822) (concat (mux (sgt v_11825 v_11826) v_11825 v_11826) (concat (mux (sgt v_11829 v_11830) v_11829 v_11830) (concat (mux (sgt v_11833 v_11834) v_11833 v_11834) (concat (mux (sgt v_11837 v_11838) v_11837 v_11838) (mux (sgt v_11841 v_11842) v_11841 v_11842))))))))))))))));
      pure ()
    pat_end
