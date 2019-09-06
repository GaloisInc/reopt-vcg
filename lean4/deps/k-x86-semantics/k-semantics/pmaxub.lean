def pmaxub1 : instruction :=
  definst "pmaxub" $ do
    pattern fun (v_2666 : reg (bv 128)) (v_2667 : reg (bv 128)) => do
      v_4917 <- getRegister v_2667;
      v_4918 <- eval (extract v_4917 0 8);
      v_4919 <- getRegister v_2666;
      v_4920 <- eval (extract v_4919 0 8);
      v_4923 <- eval (extract v_4917 8 16);
      v_4924 <- eval (extract v_4919 8 16);
      v_4927 <- eval (extract v_4917 16 24);
      v_4928 <- eval (extract v_4919 16 24);
      v_4931 <- eval (extract v_4917 24 32);
      v_4932 <- eval (extract v_4919 24 32);
      v_4935 <- eval (extract v_4917 32 40);
      v_4936 <- eval (extract v_4919 32 40);
      v_4939 <- eval (extract v_4917 40 48);
      v_4940 <- eval (extract v_4919 40 48);
      v_4943 <- eval (extract v_4917 48 56);
      v_4944 <- eval (extract v_4919 48 56);
      v_4947 <- eval (extract v_4917 56 64);
      v_4948 <- eval (extract v_4919 56 64);
      v_4951 <- eval (extract v_4917 64 72);
      v_4952 <- eval (extract v_4919 64 72);
      v_4955 <- eval (extract v_4917 72 80);
      v_4956 <- eval (extract v_4919 72 80);
      v_4959 <- eval (extract v_4917 80 88);
      v_4960 <- eval (extract v_4919 80 88);
      v_4963 <- eval (extract v_4917 88 96);
      v_4964 <- eval (extract v_4919 88 96);
      v_4967 <- eval (extract v_4917 96 104);
      v_4968 <- eval (extract v_4919 96 104);
      v_4971 <- eval (extract v_4917 104 112);
      v_4972 <- eval (extract v_4919 104 112);
      v_4975 <- eval (extract v_4917 112 120);
      v_4976 <- eval (extract v_4919 112 120);
      v_4979 <- eval (extract v_4917 120 128);
      v_4980 <- eval (extract v_4919 120 128);
      setRegister (lhs.of_reg v_2667) (concat (mux (ugt v_4918 v_4920) v_4918 v_4920) (concat (mux (ugt v_4923 v_4924) v_4923 v_4924) (concat (mux (ugt v_4927 v_4928) v_4927 v_4928) (concat (mux (ugt v_4931 v_4932) v_4931 v_4932) (concat (mux (ugt v_4935 v_4936) v_4935 v_4936) (concat (mux (ugt v_4939 v_4940) v_4939 v_4940) (concat (mux (ugt v_4943 v_4944) v_4943 v_4944) (concat (mux (ugt v_4947 v_4948) v_4947 v_4948) (concat (mux (ugt v_4951 v_4952) v_4951 v_4952) (concat (mux (ugt v_4955 v_4956) v_4955 v_4956) (concat (mux (ugt v_4959 v_4960) v_4959 v_4960) (concat (mux (ugt v_4963 v_4964) v_4963 v_4964) (concat (mux (ugt v_4967 v_4968) v_4967 v_4968) (concat (mux (ugt v_4971 v_4972) v_4971 v_4972) (concat (mux (ugt v_4975 v_4976) v_4975 v_4976) (mux (ugt v_4979 v_4980) v_4979 v_4980))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2662 : Mem) (v_2663 : reg (bv 128)) => do
      v_11761 <- getRegister v_2663;
      v_11762 <- eval (extract v_11761 0 8);
      v_11763 <- evaluateAddress v_2662;
      v_11764 <- load v_11763 16;
      v_11765 <- eval (extract v_11764 0 8);
      v_11768 <- eval (extract v_11761 8 16);
      v_11769 <- eval (extract v_11764 8 16);
      v_11772 <- eval (extract v_11761 16 24);
      v_11773 <- eval (extract v_11764 16 24);
      v_11776 <- eval (extract v_11761 24 32);
      v_11777 <- eval (extract v_11764 24 32);
      v_11780 <- eval (extract v_11761 32 40);
      v_11781 <- eval (extract v_11764 32 40);
      v_11784 <- eval (extract v_11761 40 48);
      v_11785 <- eval (extract v_11764 40 48);
      v_11788 <- eval (extract v_11761 48 56);
      v_11789 <- eval (extract v_11764 48 56);
      v_11792 <- eval (extract v_11761 56 64);
      v_11793 <- eval (extract v_11764 56 64);
      v_11796 <- eval (extract v_11761 64 72);
      v_11797 <- eval (extract v_11764 64 72);
      v_11800 <- eval (extract v_11761 72 80);
      v_11801 <- eval (extract v_11764 72 80);
      v_11804 <- eval (extract v_11761 80 88);
      v_11805 <- eval (extract v_11764 80 88);
      v_11808 <- eval (extract v_11761 88 96);
      v_11809 <- eval (extract v_11764 88 96);
      v_11812 <- eval (extract v_11761 96 104);
      v_11813 <- eval (extract v_11764 96 104);
      v_11816 <- eval (extract v_11761 104 112);
      v_11817 <- eval (extract v_11764 104 112);
      v_11820 <- eval (extract v_11761 112 120);
      v_11821 <- eval (extract v_11764 112 120);
      v_11824 <- eval (extract v_11761 120 128);
      v_11825 <- eval (extract v_11764 120 128);
      setRegister (lhs.of_reg v_2663) (concat (mux (ugt v_11762 v_11765) v_11762 v_11765) (concat (mux (ugt v_11768 v_11769) v_11768 v_11769) (concat (mux (ugt v_11772 v_11773) v_11772 v_11773) (concat (mux (ugt v_11776 v_11777) v_11776 v_11777) (concat (mux (ugt v_11780 v_11781) v_11780 v_11781) (concat (mux (ugt v_11784 v_11785) v_11784 v_11785) (concat (mux (ugt v_11788 v_11789) v_11788 v_11789) (concat (mux (ugt v_11792 v_11793) v_11792 v_11793) (concat (mux (ugt v_11796 v_11797) v_11796 v_11797) (concat (mux (ugt v_11800 v_11801) v_11800 v_11801) (concat (mux (ugt v_11804 v_11805) v_11804 v_11805) (concat (mux (ugt v_11808 v_11809) v_11808 v_11809) (concat (mux (ugt v_11812 v_11813) v_11812 v_11813) (concat (mux (ugt v_11816 v_11817) v_11816 v_11817) (concat (mux (ugt v_11820 v_11821) v_11820 v_11821) (mux (ugt v_11824 v_11825) v_11824 v_11825))))))))))))))));
      pure ()
    pat_end
