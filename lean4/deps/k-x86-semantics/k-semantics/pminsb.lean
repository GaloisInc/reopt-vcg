def pminsb1 : instruction :=
  definst "pminsb" $ do
    pattern fun (v_2616 : reg (bv 128)) (v_2617 : reg (bv 128)) => do
      v_5017 <- getRegister v_2617;
      v_5018 <- eval (extract v_5017 0 8);
      v_5019 <- getRegister v_2616;
      v_5020 <- eval (extract v_5019 0 8);
      v_5023 <- eval (extract v_5017 8 16);
      v_5024 <- eval (extract v_5019 8 16);
      v_5027 <- eval (extract v_5017 16 24);
      v_5028 <- eval (extract v_5019 16 24);
      v_5031 <- eval (extract v_5017 24 32);
      v_5032 <- eval (extract v_5019 24 32);
      v_5035 <- eval (extract v_5017 32 40);
      v_5036 <- eval (extract v_5019 32 40);
      v_5039 <- eval (extract v_5017 40 48);
      v_5040 <- eval (extract v_5019 40 48);
      v_5043 <- eval (extract v_5017 48 56);
      v_5044 <- eval (extract v_5019 48 56);
      v_5047 <- eval (extract v_5017 56 64);
      v_5048 <- eval (extract v_5019 56 64);
      v_5051 <- eval (extract v_5017 64 72);
      v_5052 <- eval (extract v_5019 64 72);
      v_5055 <- eval (extract v_5017 72 80);
      v_5056 <- eval (extract v_5019 72 80);
      v_5059 <- eval (extract v_5017 80 88);
      v_5060 <- eval (extract v_5019 80 88);
      v_5063 <- eval (extract v_5017 88 96);
      v_5064 <- eval (extract v_5019 88 96);
      v_5067 <- eval (extract v_5017 96 104);
      v_5068 <- eval (extract v_5019 96 104);
      v_5071 <- eval (extract v_5017 104 112);
      v_5072 <- eval (extract v_5019 104 112);
      v_5075 <- eval (extract v_5017 112 120);
      v_5076 <- eval (extract v_5019 112 120);
      v_5079 <- eval (extract v_5017 120 128);
      v_5080 <- eval (extract v_5019 120 128);
      setRegister (lhs.of_reg v_2617) (concat (mux (slt v_5018 v_5020) v_5018 v_5020) (concat (mux (slt v_5023 v_5024) v_5023 v_5024) (concat (mux (slt v_5027 v_5028) v_5027 v_5028) (concat (mux (slt v_5031 v_5032) v_5031 v_5032) (concat (mux (slt v_5035 v_5036) v_5035 v_5036) (concat (mux (slt v_5039 v_5040) v_5039 v_5040) (concat (mux (slt v_5043 v_5044) v_5043 v_5044) (concat (mux (slt v_5047 v_5048) v_5047 v_5048) (concat (mux (slt v_5051 v_5052) v_5051 v_5052) (concat (mux (slt v_5055 v_5056) v_5055 v_5056) (concat (mux (slt v_5059 v_5060) v_5059 v_5060) (concat (mux (slt v_5063 v_5064) v_5063 v_5064) (concat (mux (slt v_5067 v_5068) v_5067 v_5068) (concat (mux (slt v_5071 v_5072) v_5071 v_5072) (concat (mux (slt v_5075 v_5076) v_5075 v_5076) (mux (slt v_5079 v_5080) v_5079 v_5080))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2612 : Mem) (v_2613 : reg (bv 128)) => do
      v_12076 <- getRegister v_2613;
      v_12077 <- eval (extract v_12076 0 8);
      v_12078 <- evaluateAddress v_2612;
      v_12079 <- load v_12078 16;
      v_12080 <- eval (extract v_12079 0 8);
      v_12083 <- eval (extract v_12076 8 16);
      v_12084 <- eval (extract v_12079 8 16);
      v_12087 <- eval (extract v_12076 16 24);
      v_12088 <- eval (extract v_12079 16 24);
      v_12091 <- eval (extract v_12076 24 32);
      v_12092 <- eval (extract v_12079 24 32);
      v_12095 <- eval (extract v_12076 32 40);
      v_12096 <- eval (extract v_12079 32 40);
      v_12099 <- eval (extract v_12076 40 48);
      v_12100 <- eval (extract v_12079 40 48);
      v_12103 <- eval (extract v_12076 48 56);
      v_12104 <- eval (extract v_12079 48 56);
      v_12107 <- eval (extract v_12076 56 64);
      v_12108 <- eval (extract v_12079 56 64);
      v_12111 <- eval (extract v_12076 64 72);
      v_12112 <- eval (extract v_12079 64 72);
      v_12115 <- eval (extract v_12076 72 80);
      v_12116 <- eval (extract v_12079 72 80);
      v_12119 <- eval (extract v_12076 80 88);
      v_12120 <- eval (extract v_12079 80 88);
      v_12123 <- eval (extract v_12076 88 96);
      v_12124 <- eval (extract v_12079 88 96);
      v_12127 <- eval (extract v_12076 96 104);
      v_12128 <- eval (extract v_12079 96 104);
      v_12131 <- eval (extract v_12076 104 112);
      v_12132 <- eval (extract v_12079 104 112);
      v_12135 <- eval (extract v_12076 112 120);
      v_12136 <- eval (extract v_12079 112 120);
      v_12139 <- eval (extract v_12076 120 128);
      v_12140 <- eval (extract v_12079 120 128);
      setRegister (lhs.of_reg v_2613) (concat (mux (slt v_12077 v_12080) v_12077 v_12080) (concat (mux (slt v_12083 v_12084) v_12083 v_12084) (concat (mux (slt v_12087 v_12088) v_12087 v_12088) (concat (mux (slt v_12091 v_12092) v_12091 v_12092) (concat (mux (slt v_12095 v_12096) v_12095 v_12096) (concat (mux (slt v_12099 v_12100) v_12099 v_12100) (concat (mux (slt v_12103 v_12104) v_12103 v_12104) (concat (mux (slt v_12107 v_12108) v_12107 v_12108) (concat (mux (slt v_12111 v_12112) v_12111 v_12112) (concat (mux (slt v_12115 v_12116) v_12115 v_12116) (concat (mux (slt v_12119 v_12120) v_12119 v_12120) (concat (mux (slt v_12123 v_12124) v_12123 v_12124) (concat (mux (slt v_12127 v_12128) v_12127 v_12128) (concat (mux (slt v_12131 v_12132) v_12131 v_12132) (concat (mux (slt v_12135 v_12136) v_12135 v_12136) (mux (slt v_12139 v_12140) v_12139 v_12140))))))))))))))));
      pure ()
    pat_end
