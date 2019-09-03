def pmaxsw1 : instruction :=
  definst "pmaxsw" $ do
    pattern fun (v_2566 : reg (bv 128)) (v_2567 : reg (bv 128)) => do
      v_4880 <- getRegister v_2567;
      v_4881 <- eval (extract v_4880 0 16);
      v_4882 <- getRegister v_2566;
      v_4883 <- eval (extract v_4882 0 16);
      v_4886 <- eval (extract v_4880 16 32);
      v_4887 <- eval (extract v_4882 16 32);
      v_4890 <- eval (extract v_4880 32 48);
      v_4891 <- eval (extract v_4882 32 48);
      v_4894 <- eval (extract v_4880 48 64);
      v_4895 <- eval (extract v_4882 48 64);
      v_4898 <- eval (extract v_4880 64 80);
      v_4899 <- eval (extract v_4882 64 80);
      v_4902 <- eval (extract v_4880 80 96);
      v_4903 <- eval (extract v_4882 80 96);
      v_4906 <- eval (extract v_4880 96 112);
      v_4907 <- eval (extract v_4882 96 112);
      v_4910 <- eval (extract v_4880 112 128);
      v_4911 <- eval (extract v_4882 112 128);
      setRegister (lhs.of_reg v_2567) (concat (mux (sgt v_4881 v_4883) v_4881 v_4883) (concat (mux (sgt v_4886 v_4887) v_4886 v_4887) (concat (mux (sgt v_4890 v_4891) v_4890 v_4891) (concat (mux (sgt v_4894 v_4895) v_4894 v_4895) (concat (mux (sgt v_4898 v_4899) v_4898 v_4899) (concat (mux (sgt v_4902 v_4903) v_4902 v_4903) (concat (mux (sgt v_4906 v_4907) v_4906 v_4907) (mux (sgt v_4910 v_4911) v_4910 v_4911))))))));
      pure ()
    pat_end;
    pattern fun (v_2561 : Mem) (v_2562 : reg (bv 128)) => do
      v_12277 <- getRegister v_2562;
      v_12278 <- eval (extract v_12277 0 16);
      v_12279 <- evaluateAddress v_2561;
      v_12280 <- load v_12279 16;
      v_12281 <- eval (extract v_12280 0 16);
      v_12284 <- eval (extract v_12277 16 32);
      v_12285 <- eval (extract v_12280 16 32);
      v_12288 <- eval (extract v_12277 32 48);
      v_12289 <- eval (extract v_12280 32 48);
      v_12292 <- eval (extract v_12277 48 64);
      v_12293 <- eval (extract v_12280 48 64);
      v_12296 <- eval (extract v_12277 64 80);
      v_12297 <- eval (extract v_12280 64 80);
      v_12300 <- eval (extract v_12277 80 96);
      v_12301 <- eval (extract v_12280 80 96);
      v_12304 <- eval (extract v_12277 96 112);
      v_12305 <- eval (extract v_12280 96 112);
      v_12308 <- eval (extract v_12277 112 128);
      v_12309 <- eval (extract v_12280 112 128);
      setRegister (lhs.of_reg v_2562) (concat (mux (sgt v_12278 v_12281) v_12278 v_12281) (concat (mux (sgt v_12284 v_12285) v_12284 v_12285) (concat (mux (sgt v_12288 v_12289) v_12288 v_12289) (concat (mux (sgt v_12292 v_12293) v_12292 v_12293) (concat (mux (sgt v_12296 v_12297) v_12296 v_12297) (concat (mux (sgt v_12300 v_12301) v_12300 v_12301) (concat (mux (sgt v_12304 v_12305) v_12304 v_12305) (mux (sgt v_12308 v_12309) v_12308 v_12309))))))));
      pure ()
    pat_end
