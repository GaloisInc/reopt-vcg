def pmaxsw1 : instruction :=
  definst "pmaxsw" $ do
    pattern fun (v_2629 : reg (bv 128)) (v_2630 : reg (bv 128)) => do
      v_4844 <- getRegister v_2630;
      v_4845 <- eval (extract v_4844 0 16);
      v_4846 <- getRegister v_2629;
      v_4847 <- eval (extract v_4846 0 16);
      v_4850 <- eval (extract v_4844 16 32);
      v_4851 <- eval (extract v_4846 16 32);
      v_4854 <- eval (extract v_4844 32 48);
      v_4855 <- eval (extract v_4846 32 48);
      v_4858 <- eval (extract v_4844 48 64);
      v_4859 <- eval (extract v_4846 48 64);
      v_4862 <- eval (extract v_4844 64 80);
      v_4863 <- eval (extract v_4846 64 80);
      v_4866 <- eval (extract v_4844 80 96);
      v_4867 <- eval (extract v_4846 80 96);
      v_4870 <- eval (extract v_4844 96 112);
      v_4871 <- eval (extract v_4846 96 112);
      v_4874 <- eval (extract v_4844 112 128);
      v_4875 <- eval (extract v_4846 112 128);
      setRegister (lhs.of_reg v_2630) (concat (mux (sgt v_4845 v_4847) v_4845 v_4847) (concat (mux (sgt v_4850 v_4851) v_4850 v_4851) (concat (mux (sgt v_4854 v_4855) v_4854 v_4855) (concat (mux (sgt v_4858 v_4859) v_4858 v_4859) (concat (mux (sgt v_4862 v_4863) v_4862 v_4863) (concat (mux (sgt v_4866 v_4867) v_4866 v_4867) (concat (mux (sgt v_4870 v_4871) v_4870 v_4871) (mux (sgt v_4874 v_4875) v_4874 v_4875))))))));
      pure ()
    pat_end;
    pattern fun (v_2626 : Mem) (v_2625 : reg (bv 128)) => do
      v_11742 <- getRegister v_2625;
      v_11743 <- eval (extract v_11742 0 16);
      v_11744 <- evaluateAddress v_2626;
      v_11745 <- load v_11744 16;
      v_11746 <- eval (extract v_11745 0 16);
      v_11749 <- eval (extract v_11742 16 32);
      v_11750 <- eval (extract v_11745 16 32);
      v_11753 <- eval (extract v_11742 32 48);
      v_11754 <- eval (extract v_11745 32 48);
      v_11757 <- eval (extract v_11742 48 64);
      v_11758 <- eval (extract v_11745 48 64);
      v_11761 <- eval (extract v_11742 64 80);
      v_11762 <- eval (extract v_11745 64 80);
      v_11765 <- eval (extract v_11742 80 96);
      v_11766 <- eval (extract v_11745 80 96);
      v_11769 <- eval (extract v_11742 96 112);
      v_11770 <- eval (extract v_11745 96 112);
      v_11773 <- eval (extract v_11742 112 128);
      v_11774 <- eval (extract v_11745 112 128);
      setRegister (lhs.of_reg v_2625) (concat (mux (sgt v_11743 v_11746) v_11743 v_11746) (concat (mux (sgt v_11749 v_11750) v_11749 v_11750) (concat (mux (sgt v_11753 v_11754) v_11753 v_11754) (concat (mux (sgt v_11757 v_11758) v_11757 v_11758) (concat (mux (sgt v_11761 v_11762) v_11761 v_11762) (concat (mux (sgt v_11765 v_11766) v_11765 v_11766) (concat (mux (sgt v_11769 v_11770) v_11769 v_11770) (mux (sgt v_11773 v_11774) v_11773 v_11774))))))));
      pure ()
    pat_end
