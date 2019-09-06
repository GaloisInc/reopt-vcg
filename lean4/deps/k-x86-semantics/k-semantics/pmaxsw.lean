def pmaxsw1 : instruction :=
  definst "pmaxsw" $ do
    pattern fun (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) => do
      v_4871 <- getRegister v_2658;
      v_4872 <- eval (extract v_4871 0 16);
      v_4873 <- getRegister v_2657;
      v_4874 <- eval (extract v_4873 0 16);
      v_4877 <- eval (extract v_4871 16 32);
      v_4878 <- eval (extract v_4873 16 32);
      v_4881 <- eval (extract v_4871 32 48);
      v_4882 <- eval (extract v_4873 32 48);
      v_4885 <- eval (extract v_4871 48 64);
      v_4886 <- eval (extract v_4873 48 64);
      v_4889 <- eval (extract v_4871 64 80);
      v_4890 <- eval (extract v_4873 64 80);
      v_4893 <- eval (extract v_4871 80 96);
      v_4894 <- eval (extract v_4873 80 96);
      v_4897 <- eval (extract v_4871 96 112);
      v_4898 <- eval (extract v_4873 96 112);
      v_4901 <- eval (extract v_4871 112 128);
      v_4902 <- eval (extract v_4873 112 128);
      setRegister (lhs.of_reg v_2658) (concat (mux (sgt v_4872 v_4874) v_4872 v_4874) (concat (mux (sgt v_4877 v_4878) v_4877 v_4878) (concat (mux (sgt v_4881 v_4882) v_4881 v_4882) (concat (mux (sgt v_4885 v_4886) v_4885 v_4886) (concat (mux (sgt v_4889 v_4890) v_4889 v_4890) (concat (mux (sgt v_4893 v_4894) v_4893 v_4894) (concat (mux (sgt v_4897 v_4898) v_4897 v_4898) (mux (sgt v_4901 v_4902) v_4901 v_4902))))))));
      pure ()
    pat_end;
    pattern fun (v_2653 : Mem) (v_2654 : reg (bv 128)) => do
      v_11718 <- getRegister v_2654;
      v_11719 <- eval (extract v_11718 0 16);
      v_11720 <- evaluateAddress v_2653;
      v_11721 <- load v_11720 16;
      v_11722 <- eval (extract v_11721 0 16);
      v_11725 <- eval (extract v_11718 16 32);
      v_11726 <- eval (extract v_11721 16 32);
      v_11729 <- eval (extract v_11718 32 48);
      v_11730 <- eval (extract v_11721 32 48);
      v_11733 <- eval (extract v_11718 48 64);
      v_11734 <- eval (extract v_11721 48 64);
      v_11737 <- eval (extract v_11718 64 80);
      v_11738 <- eval (extract v_11721 64 80);
      v_11741 <- eval (extract v_11718 80 96);
      v_11742 <- eval (extract v_11721 80 96);
      v_11745 <- eval (extract v_11718 96 112);
      v_11746 <- eval (extract v_11721 96 112);
      v_11749 <- eval (extract v_11718 112 128);
      v_11750 <- eval (extract v_11721 112 128);
      setRegister (lhs.of_reg v_2654) (concat (mux (sgt v_11719 v_11722) v_11719 v_11722) (concat (mux (sgt v_11725 v_11726) v_11725 v_11726) (concat (mux (sgt v_11729 v_11730) v_11729 v_11730) (concat (mux (sgt v_11733 v_11734) v_11733 v_11734) (concat (mux (sgt v_11737 v_11738) v_11737 v_11738) (concat (mux (sgt v_11741 v_11742) v_11741 v_11742) (concat (mux (sgt v_11745 v_11746) v_11745 v_11746) (mux (sgt v_11749 v_11750) v_11749 v_11750))))))));
      pure ()
    pat_end
