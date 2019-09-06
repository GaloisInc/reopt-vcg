def pminub1 : instruction :=
  definst "pminub" $ do
    pattern fun (v_2720 : reg (bv 128)) (v_2721 : reg (bv 128)) => do
      v_5233 <- getRegister v_2721;
      v_5234 <- eval (extract v_5233 0 8);
      v_5235 <- getRegister v_2720;
      v_5236 <- eval (extract v_5235 0 8);
      v_5239 <- eval (extract v_5233 8 16);
      v_5240 <- eval (extract v_5235 8 16);
      v_5243 <- eval (extract v_5233 16 24);
      v_5244 <- eval (extract v_5235 16 24);
      v_5247 <- eval (extract v_5233 24 32);
      v_5248 <- eval (extract v_5235 24 32);
      v_5251 <- eval (extract v_5233 32 40);
      v_5252 <- eval (extract v_5235 32 40);
      v_5255 <- eval (extract v_5233 40 48);
      v_5256 <- eval (extract v_5235 40 48);
      v_5259 <- eval (extract v_5233 48 56);
      v_5260 <- eval (extract v_5235 48 56);
      v_5263 <- eval (extract v_5233 56 64);
      v_5264 <- eval (extract v_5235 56 64);
      v_5267 <- eval (extract v_5233 64 72);
      v_5268 <- eval (extract v_5235 64 72);
      v_5271 <- eval (extract v_5233 72 80);
      v_5272 <- eval (extract v_5235 72 80);
      v_5275 <- eval (extract v_5233 80 88);
      v_5276 <- eval (extract v_5235 80 88);
      v_5279 <- eval (extract v_5233 88 96);
      v_5280 <- eval (extract v_5235 88 96);
      v_5283 <- eval (extract v_5233 96 104);
      v_5284 <- eval (extract v_5235 96 104);
      v_5287 <- eval (extract v_5233 104 112);
      v_5288 <- eval (extract v_5235 104 112);
      v_5291 <- eval (extract v_5233 112 120);
      v_5292 <- eval (extract v_5235 112 120);
      v_5295 <- eval (extract v_5233 120 128);
      v_5296 <- eval (extract v_5235 120 128);
      setRegister (lhs.of_reg v_2721) (concat (mux (ult v_5234 v_5236) v_5234 v_5236) (concat (mux (ult v_5239 v_5240) v_5239 v_5240) (concat (mux (ult v_5243 v_5244) v_5243 v_5244) (concat (mux (ult v_5247 v_5248) v_5247 v_5248) (concat (mux (ult v_5251 v_5252) v_5251 v_5252) (concat (mux (ult v_5255 v_5256) v_5255 v_5256) (concat (mux (ult v_5259 v_5260) v_5259 v_5260) (concat (mux (ult v_5263 v_5264) v_5263 v_5264) (concat (mux (ult v_5267 v_5268) v_5267 v_5268) (concat (mux (ult v_5271 v_5272) v_5271 v_5272) (concat (mux (ult v_5275 v_5276) v_5275 v_5276) (concat (mux (ult v_5279 v_5280) v_5279 v_5280) (concat (mux (ult v_5283 v_5284) v_5283 v_5284) (concat (mux (ult v_5287 v_5288) v_5287 v_5288) (concat (mux (ult v_5291 v_5292) v_5291 v_5292) (mux (ult v_5295 v_5296) v_5295 v_5296))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2716 : Mem) (v_2717 : reg (bv 128)) => do
      v_12059 <- getRegister v_2717;
      v_12060 <- eval (extract v_12059 0 8);
      v_12061 <- evaluateAddress v_2716;
      v_12062 <- load v_12061 16;
      v_12063 <- eval (extract v_12062 0 8);
      v_12066 <- eval (extract v_12059 8 16);
      v_12067 <- eval (extract v_12062 8 16);
      v_12070 <- eval (extract v_12059 16 24);
      v_12071 <- eval (extract v_12062 16 24);
      v_12074 <- eval (extract v_12059 24 32);
      v_12075 <- eval (extract v_12062 24 32);
      v_12078 <- eval (extract v_12059 32 40);
      v_12079 <- eval (extract v_12062 32 40);
      v_12082 <- eval (extract v_12059 40 48);
      v_12083 <- eval (extract v_12062 40 48);
      v_12086 <- eval (extract v_12059 48 56);
      v_12087 <- eval (extract v_12062 48 56);
      v_12090 <- eval (extract v_12059 56 64);
      v_12091 <- eval (extract v_12062 56 64);
      v_12094 <- eval (extract v_12059 64 72);
      v_12095 <- eval (extract v_12062 64 72);
      v_12098 <- eval (extract v_12059 72 80);
      v_12099 <- eval (extract v_12062 72 80);
      v_12102 <- eval (extract v_12059 80 88);
      v_12103 <- eval (extract v_12062 80 88);
      v_12106 <- eval (extract v_12059 88 96);
      v_12107 <- eval (extract v_12062 88 96);
      v_12110 <- eval (extract v_12059 96 104);
      v_12111 <- eval (extract v_12062 96 104);
      v_12114 <- eval (extract v_12059 104 112);
      v_12115 <- eval (extract v_12062 104 112);
      v_12118 <- eval (extract v_12059 112 120);
      v_12119 <- eval (extract v_12062 112 120);
      v_12122 <- eval (extract v_12059 120 128);
      v_12123 <- eval (extract v_12062 120 128);
      setRegister (lhs.of_reg v_2717) (concat (mux (ult v_12060 v_12063) v_12060 v_12063) (concat (mux (ult v_12066 v_12067) v_12066 v_12067) (concat (mux (ult v_12070 v_12071) v_12070 v_12071) (concat (mux (ult v_12074 v_12075) v_12074 v_12075) (concat (mux (ult v_12078 v_12079) v_12078 v_12079) (concat (mux (ult v_12082 v_12083) v_12082 v_12083) (concat (mux (ult v_12086 v_12087) v_12086 v_12087) (concat (mux (ult v_12090 v_12091) v_12090 v_12091) (concat (mux (ult v_12094 v_12095) v_12094 v_12095) (concat (mux (ult v_12098 v_12099) v_12098 v_12099) (concat (mux (ult v_12102 v_12103) v_12102 v_12103) (concat (mux (ult v_12106 v_12107) v_12106 v_12107) (concat (mux (ult v_12110 v_12111) v_12110 v_12111) (concat (mux (ult v_12114 v_12115) v_12114 v_12115) (concat (mux (ult v_12118 v_12119) v_12118 v_12119) (mux (ult v_12122 v_12123) v_12122 v_12123))))))))))))))));
      pure ()
    pat_end
