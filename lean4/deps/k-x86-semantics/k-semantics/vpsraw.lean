def vpsraw1 : instruction :=
  definst "vpsraw" $ do
    pattern fun (v_3250 : imm int) (v_3248 : reg (bv 128)) (v_3249 : reg (bv 128)) => do
      v_8895 <- getRegister v_3248;
      v_8896 <- eval (extract v_8895 0 16);
      v_8900 <- eval (handleImmediateWithSignExtend v_3250 8 8);
      v_8905 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8900) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8900)));
      v_8907 <- eval (extract v_8895 16 32);
      v_8912 <- eval (extract v_8895 32 48);
      v_8917 <- eval (extract v_8895 48 64);
      v_8922 <- eval (extract v_8895 64 80);
      v_8927 <- eval (extract v_8895 80 96);
      v_8932 <- eval (extract v_8895 96 112);
      v_8937 <- eval (extract v_8895 112 128);
      setRegister (lhs.of_reg v_3249) (concat (ashr (mi (bitwidthMInt v_8896) (svalueMInt v_8896)) v_8905) (concat (ashr (mi (bitwidthMInt v_8907) (svalueMInt v_8907)) v_8905) (concat (ashr (mi (bitwidthMInt v_8912) (svalueMInt v_8912)) v_8905) (concat (ashr (mi (bitwidthMInt v_8917) (svalueMInt v_8917)) v_8905) (concat (ashr (mi (bitwidthMInt v_8922) (svalueMInt v_8922)) v_8905) (concat (ashr (mi (bitwidthMInt v_8927) (svalueMInt v_8927)) v_8905) (concat (ashr (mi (bitwidthMInt v_8932) (svalueMInt v_8932)) v_8905) (ashr (mi (bitwidthMInt v_8937) (svalueMInt v_8937)) v_8905))))))));
      pure ()
    pat_end;
    pattern fun (v_3259 : reg (bv 128)) (v_3260 : reg (bv 128)) (v_3261 : reg (bv 128)) => do
      v_8955 <- getRegister v_3260;
      v_8956 <- eval (extract v_8955 0 16);
      v_8960 <- getRegister v_3259;
      v_8965 <- eval (uvalueMInt (mux (ugt (extract v_8960 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8960 112 128)));
      v_8967 <- eval (extract v_8955 16 32);
      v_8972 <- eval (extract v_8955 32 48);
      v_8977 <- eval (extract v_8955 48 64);
      v_8982 <- eval (extract v_8955 64 80);
      v_8987 <- eval (extract v_8955 80 96);
      v_8992 <- eval (extract v_8955 96 112);
      v_8997 <- eval (extract v_8955 112 128);
      setRegister (lhs.of_reg v_3261) (concat (ashr (mi (bitwidthMInt v_8956) (svalueMInt v_8956)) v_8965) (concat (ashr (mi (bitwidthMInt v_8967) (svalueMInt v_8967)) v_8965) (concat (ashr (mi (bitwidthMInt v_8972) (svalueMInt v_8972)) v_8965) (concat (ashr (mi (bitwidthMInt v_8977) (svalueMInt v_8977)) v_8965) (concat (ashr (mi (bitwidthMInt v_8982) (svalueMInt v_8982)) v_8965) (concat (ashr (mi (bitwidthMInt v_8987) (svalueMInt v_8987)) v_8965) (concat (ashr (mi (bitwidthMInt v_8992) (svalueMInt v_8992)) v_8965) (ashr (mi (bitwidthMInt v_8997) (svalueMInt v_8997)) v_8965))))))));
      pure ()
    pat_end;
    pattern fun (v_3265 : imm int) (v_3266 : reg (bv 256)) (v_3267 : reg (bv 256)) => do
      v_9010 <- getRegister v_3266;
      v_9011 <- eval (extract v_9010 0 16);
      v_9015 <- eval (handleImmediateWithSignExtend v_3265 8 8);
      v_9020 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_9015) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_9015)));
      v_9022 <- eval (extract v_9010 16 32);
      v_9027 <- eval (extract v_9010 32 48);
      v_9032 <- eval (extract v_9010 48 64);
      v_9037 <- eval (extract v_9010 64 80);
      v_9042 <- eval (extract v_9010 80 96);
      v_9047 <- eval (extract v_9010 96 112);
      v_9052 <- eval (extract v_9010 112 128);
      v_9057 <- eval (extract v_9010 128 144);
      v_9062 <- eval (extract v_9010 144 160);
      v_9067 <- eval (extract v_9010 160 176);
      v_9072 <- eval (extract v_9010 176 192);
      v_9077 <- eval (extract v_9010 192 208);
      v_9082 <- eval (extract v_9010 208 224);
      v_9087 <- eval (extract v_9010 224 240);
      v_9092 <- eval (extract v_9010 240 256);
      setRegister (lhs.of_reg v_3267) (concat (ashr (mi (bitwidthMInt v_9011) (svalueMInt v_9011)) v_9020) (concat (ashr (mi (bitwidthMInt v_9022) (svalueMInt v_9022)) v_9020) (concat (ashr (mi (bitwidthMInt v_9027) (svalueMInt v_9027)) v_9020) (concat (ashr (mi (bitwidthMInt v_9032) (svalueMInt v_9032)) v_9020) (concat (ashr (mi (bitwidthMInt v_9037) (svalueMInt v_9037)) v_9020) (concat (ashr (mi (bitwidthMInt v_9042) (svalueMInt v_9042)) v_9020) (concat (ashr (mi (bitwidthMInt v_9047) (svalueMInt v_9047)) v_9020) (concat (ashr (mi (bitwidthMInt v_9052) (svalueMInt v_9052)) v_9020) (concat (ashr (mi (bitwidthMInt v_9057) (svalueMInt v_9057)) v_9020) (concat (ashr (mi (bitwidthMInt v_9062) (svalueMInt v_9062)) v_9020) (concat (ashr (mi (bitwidthMInt v_9067) (svalueMInt v_9067)) v_9020) (concat (ashr (mi (bitwidthMInt v_9072) (svalueMInt v_9072)) v_9020) (concat (ashr (mi (bitwidthMInt v_9077) (svalueMInt v_9077)) v_9020) (concat (ashr (mi (bitwidthMInt v_9082) (svalueMInt v_9082)) v_9020) (concat (ashr (mi (bitwidthMInt v_9087) (svalueMInt v_9087)) v_9020) (ashr (mi (bitwidthMInt v_9092) (svalueMInt v_9092)) v_9020))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3276 : reg (bv 128)) (v_3277 : reg (bv 256)) (v_3278 : reg (bv 256)) => do
      v_9118 <- getRegister v_3277;
      v_9119 <- eval (extract v_9118 0 16);
      v_9123 <- getRegister v_3276;
      v_9128 <- eval (uvalueMInt (mux (ugt (extract v_9123 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_9123 112 128)));
      v_9130 <- eval (extract v_9118 16 32);
      v_9135 <- eval (extract v_9118 32 48);
      v_9140 <- eval (extract v_9118 48 64);
      v_9145 <- eval (extract v_9118 64 80);
      v_9150 <- eval (extract v_9118 80 96);
      v_9155 <- eval (extract v_9118 96 112);
      v_9160 <- eval (extract v_9118 112 128);
      v_9165 <- eval (extract v_9118 128 144);
      v_9170 <- eval (extract v_9118 144 160);
      v_9175 <- eval (extract v_9118 160 176);
      v_9180 <- eval (extract v_9118 176 192);
      v_9185 <- eval (extract v_9118 192 208);
      v_9190 <- eval (extract v_9118 208 224);
      v_9195 <- eval (extract v_9118 224 240);
      v_9200 <- eval (extract v_9118 240 256);
      setRegister (lhs.of_reg v_3278) (concat (ashr (mi (bitwidthMInt v_9119) (svalueMInt v_9119)) v_9128) (concat (ashr (mi (bitwidthMInt v_9130) (svalueMInt v_9130)) v_9128) (concat (ashr (mi (bitwidthMInt v_9135) (svalueMInt v_9135)) v_9128) (concat (ashr (mi (bitwidthMInt v_9140) (svalueMInt v_9140)) v_9128) (concat (ashr (mi (bitwidthMInt v_9145) (svalueMInt v_9145)) v_9128) (concat (ashr (mi (bitwidthMInt v_9150) (svalueMInt v_9150)) v_9128) (concat (ashr (mi (bitwidthMInt v_9155) (svalueMInt v_9155)) v_9128) (concat (ashr (mi (bitwidthMInt v_9160) (svalueMInt v_9160)) v_9128) (concat (ashr (mi (bitwidthMInt v_9165) (svalueMInt v_9165)) v_9128) (concat (ashr (mi (bitwidthMInt v_9170) (svalueMInt v_9170)) v_9128) (concat (ashr (mi (bitwidthMInt v_9175) (svalueMInt v_9175)) v_9128) (concat (ashr (mi (bitwidthMInt v_9180) (svalueMInt v_9180)) v_9128) (concat (ashr (mi (bitwidthMInt v_9185) (svalueMInt v_9185)) v_9128) (concat (ashr (mi (bitwidthMInt v_9190) (svalueMInt v_9190)) v_9128) (concat (ashr (mi (bitwidthMInt v_9195) (svalueMInt v_9195)) v_9128) (ashr (mi (bitwidthMInt v_9200) (svalueMInt v_9200)) v_9128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3256 : Mem) (v_3254 : reg (bv 128)) (v_3255 : reg (bv 128)) => do
      v_15497 <- getRegister v_3254;
      v_15498 <- eval (extract v_15497 0 16);
      v_15502 <- evaluateAddress v_3256;
      v_15503 <- load v_15502 16;
      v_15508 <- eval (uvalueMInt (mux (ugt (extract v_15503 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_15503 112 128)));
      v_15510 <- eval (extract v_15497 16 32);
      v_15515 <- eval (extract v_15497 32 48);
      v_15520 <- eval (extract v_15497 48 64);
      v_15525 <- eval (extract v_15497 64 80);
      v_15530 <- eval (extract v_15497 80 96);
      v_15535 <- eval (extract v_15497 96 112);
      v_15540 <- eval (extract v_15497 112 128);
      setRegister (lhs.of_reg v_3255) (concat (ashr (mi (bitwidthMInt v_15498) (svalueMInt v_15498)) v_15508) (concat (ashr (mi (bitwidthMInt v_15510) (svalueMInt v_15510)) v_15508) (concat (ashr (mi (bitwidthMInt v_15515) (svalueMInt v_15515)) v_15508) (concat (ashr (mi (bitwidthMInt v_15520) (svalueMInt v_15520)) v_15508) (concat (ashr (mi (bitwidthMInt v_15525) (svalueMInt v_15525)) v_15508) (concat (ashr (mi (bitwidthMInt v_15530) (svalueMInt v_15530)) v_15508) (concat (ashr (mi (bitwidthMInt v_15535) (svalueMInt v_15535)) v_15508) (ashr (mi (bitwidthMInt v_15540) (svalueMInt v_15540)) v_15508))))))));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3272 : reg (bv 256)) (v_3273 : reg (bv 256)) => do
      v_15553 <- getRegister v_3272;
      v_15554 <- eval (extract v_15553 0 16);
      v_15558 <- evaluateAddress v_3271;
      v_15559 <- load v_15558 16;
      v_15564 <- eval (uvalueMInt (mux (ugt (extract v_15559 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_15559 112 128)));
      v_15566 <- eval (extract v_15553 16 32);
      v_15571 <- eval (extract v_15553 32 48);
      v_15576 <- eval (extract v_15553 48 64);
      v_15581 <- eval (extract v_15553 64 80);
      v_15586 <- eval (extract v_15553 80 96);
      v_15591 <- eval (extract v_15553 96 112);
      v_15596 <- eval (extract v_15553 112 128);
      v_15601 <- eval (extract v_15553 128 144);
      v_15606 <- eval (extract v_15553 144 160);
      v_15611 <- eval (extract v_15553 160 176);
      v_15616 <- eval (extract v_15553 176 192);
      v_15621 <- eval (extract v_15553 192 208);
      v_15626 <- eval (extract v_15553 208 224);
      v_15631 <- eval (extract v_15553 224 240);
      v_15636 <- eval (extract v_15553 240 256);
      setRegister (lhs.of_reg v_3273) (concat (ashr (mi (bitwidthMInt v_15554) (svalueMInt v_15554)) v_15564) (concat (ashr (mi (bitwidthMInt v_15566) (svalueMInt v_15566)) v_15564) (concat (ashr (mi (bitwidthMInt v_15571) (svalueMInt v_15571)) v_15564) (concat (ashr (mi (bitwidthMInt v_15576) (svalueMInt v_15576)) v_15564) (concat (ashr (mi (bitwidthMInt v_15581) (svalueMInt v_15581)) v_15564) (concat (ashr (mi (bitwidthMInt v_15586) (svalueMInt v_15586)) v_15564) (concat (ashr (mi (bitwidthMInt v_15591) (svalueMInt v_15591)) v_15564) (concat (ashr (mi (bitwidthMInt v_15596) (svalueMInt v_15596)) v_15564) (concat (ashr (mi (bitwidthMInt v_15601) (svalueMInt v_15601)) v_15564) (concat (ashr (mi (bitwidthMInt v_15606) (svalueMInt v_15606)) v_15564) (concat (ashr (mi (bitwidthMInt v_15611) (svalueMInt v_15611)) v_15564) (concat (ashr (mi (bitwidthMInt v_15616) (svalueMInt v_15616)) v_15564) (concat (ashr (mi (bitwidthMInt v_15621) (svalueMInt v_15621)) v_15564) (concat (ashr (mi (bitwidthMInt v_15626) (svalueMInt v_15626)) v_15564) (concat (ashr (mi (bitwidthMInt v_15631) (svalueMInt v_15631)) v_15564) (ashr (mi (bitwidthMInt v_15636) (svalueMInt v_15636)) v_15564))))))))))))))));
      pure ()
    pat_end
