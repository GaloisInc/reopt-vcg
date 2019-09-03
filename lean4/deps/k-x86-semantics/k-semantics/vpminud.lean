def vpminud1 : instruction :=
  definst "vpminud" $ do
    pattern fun (v_2540 : reg (bv 128)) (v_2541 : reg (bv 128)) (v_2542 : reg (bv 128)) => do
      v_5011 <- getRegister v_2541;
      v_5012 <- eval (extract v_5011 0 32);
      v_5013 <- getRegister v_2540;
      v_5014 <- eval (extract v_5013 0 32);
      v_5017 <- eval (extract v_5011 32 64);
      v_5018 <- eval (extract v_5013 32 64);
      v_5021 <- eval (extract v_5011 64 96);
      v_5022 <- eval (extract v_5013 64 96);
      v_5025 <- eval (extract v_5011 96 128);
      v_5026 <- eval (extract v_5013 96 128);
      setRegister (lhs.of_reg v_2542) (concat (mux (ult v_5012 v_5014) v_5012 v_5014) (concat (mux (ult v_5017 v_5018) v_5017 v_5018) (concat (mux (ult v_5021 v_5022) v_5021 v_5022) (mux (ult v_5025 v_5026) v_5025 v_5026))));
      pure ()
    pat_end;
    pattern fun (v_2552 : reg (bv 256)) (v_2553 : reg (bv 256)) (v_2554 : reg (bv 256)) => do
      v_5038 <- getRegister v_2553;
      v_5039 <- eval (extract v_5038 0 32);
      v_5040 <- getRegister v_2552;
      v_5041 <- eval (extract v_5040 0 32);
      v_5044 <- eval (extract v_5038 32 64);
      v_5045 <- eval (extract v_5040 32 64);
      v_5048 <- eval (extract v_5038 64 96);
      v_5049 <- eval (extract v_5040 64 96);
      v_5052 <- eval (extract v_5038 96 128);
      v_5053 <- eval (extract v_5040 96 128);
      v_5056 <- eval (extract v_5038 128 160);
      v_5057 <- eval (extract v_5040 128 160);
      v_5060 <- eval (extract v_5038 160 192);
      v_5061 <- eval (extract v_5040 160 192);
      v_5064 <- eval (extract v_5038 192 224);
      v_5065 <- eval (extract v_5040 192 224);
      v_5068 <- eval (extract v_5038 224 256);
      v_5069 <- eval (extract v_5040 224 256);
      setRegister (lhs.of_reg v_2554) (concat (mux (ult v_5039 v_5041) v_5039 v_5041) (concat (mux (ult v_5044 v_5045) v_5044 v_5045) (concat (mux (ult v_5048 v_5049) v_5048 v_5049) (concat (mux (ult v_5052 v_5053) v_5052 v_5053) (concat (mux (ult v_5056 v_5057) v_5056 v_5057) (concat (mux (ult v_5060 v_5061) v_5060 v_5061) (concat (mux (ult v_5064 v_5065) v_5064 v_5065) (mux (ult v_5068 v_5069) v_5068 v_5069))))))));
      pure ()
    pat_end;
    pattern fun (v_2534 : Mem) (v_2535 : reg (bv 128)) (v_2536 : reg (bv 128)) => do
      v_11912 <- getRegister v_2535;
      v_11913 <- eval (extract v_11912 0 32);
      v_11914 <- evaluateAddress v_2534;
      v_11915 <- load v_11914 16;
      v_11916 <- eval (extract v_11915 0 32);
      v_11919 <- eval (extract v_11912 32 64);
      v_11920 <- eval (extract v_11915 32 64);
      v_11923 <- eval (extract v_11912 64 96);
      v_11924 <- eval (extract v_11915 64 96);
      v_11927 <- eval (extract v_11912 96 128);
      v_11928 <- eval (extract v_11915 96 128);
      setRegister (lhs.of_reg v_2536) (concat (mux (ult v_11913 v_11916) v_11913 v_11916) (concat (mux (ult v_11919 v_11920) v_11919 v_11920) (concat (mux (ult v_11923 v_11924) v_11923 v_11924) (mux (ult v_11927 v_11928) v_11927 v_11928))));
      pure ()
    pat_end;
    pattern fun (v_2545 : Mem) (v_2547 : reg (bv 256)) (v_2548 : reg (bv 256)) => do
      v_11935 <- getRegister v_2547;
      v_11936 <- eval (extract v_11935 0 32);
      v_11937 <- evaluateAddress v_2545;
      v_11938 <- load v_11937 32;
      v_11939 <- eval (extract v_11938 0 32);
      v_11942 <- eval (extract v_11935 32 64);
      v_11943 <- eval (extract v_11938 32 64);
      v_11946 <- eval (extract v_11935 64 96);
      v_11947 <- eval (extract v_11938 64 96);
      v_11950 <- eval (extract v_11935 96 128);
      v_11951 <- eval (extract v_11938 96 128);
      v_11954 <- eval (extract v_11935 128 160);
      v_11955 <- eval (extract v_11938 128 160);
      v_11958 <- eval (extract v_11935 160 192);
      v_11959 <- eval (extract v_11938 160 192);
      v_11962 <- eval (extract v_11935 192 224);
      v_11963 <- eval (extract v_11938 192 224);
      v_11966 <- eval (extract v_11935 224 256);
      v_11967 <- eval (extract v_11938 224 256);
      setRegister (lhs.of_reg v_2548) (concat (mux (ult v_11936 v_11939) v_11936 v_11939) (concat (mux (ult v_11942 v_11943) v_11942 v_11943) (concat (mux (ult v_11946 v_11947) v_11946 v_11947) (concat (mux (ult v_11950 v_11951) v_11950 v_11951) (concat (mux (ult v_11954 v_11955) v_11954 v_11955) (concat (mux (ult v_11958 v_11959) v_11958 v_11959) (concat (mux (ult v_11962 v_11963) v_11962 v_11963) (mux (ult v_11966 v_11967) v_11966 v_11967))))))));
      pure ()
    pat_end
