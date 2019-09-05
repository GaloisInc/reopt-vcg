def pminub1 : instruction :=
  definst "pminub" $ do
    pattern fun (v_2692 : reg (bv 128)) (v_2693 : reg (bv 128)) => do
      v_5206 <- getRegister v_2693;
      v_5207 <- eval (extract v_5206 0 8);
      v_5208 <- getRegister v_2692;
      v_5209 <- eval (extract v_5208 0 8);
      v_5212 <- eval (extract v_5206 8 16);
      v_5213 <- eval (extract v_5208 8 16);
      v_5216 <- eval (extract v_5206 16 24);
      v_5217 <- eval (extract v_5208 16 24);
      v_5220 <- eval (extract v_5206 24 32);
      v_5221 <- eval (extract v_5208 24 32);
      v_5224 <- eval (extract v_5206 32 40);
      v_5225 <- eval (extract v_5208 32 40);
      v_5228 <- eval (extract v_5206 40 48);
      v_5229 <- eval (extract v_5208 40 48);
      v_5232 <- eval (extract v_5206 48 56);
      v_5233 <- eval (extract v_5208 48 56);
      v_5236 <- eval (extract v_5206 56 64);
      v_5237 <- eval (extract v_5208 56 64);
      v_5240 <- eval (extract v_5206 64 72);
      v_5241 <- eval (extract v_5208 64 72);
      v_5244 <- eval (extract v_5206 72 80);
      v_5245 <- eval (extract v_5208 72 80);
      v_5248 <- eval (extract v_5206 80 88);
      v_5249 <- eval (extract v_5208 80 88);
      v_5252 <- eval (extract v_5206 88 96);
      v_5253 <- eval (extract v_5208 88 96);
      v_5256 <- eval (extract v_5206 96 104);
      v_5257 <- eval (extract v_5208 96 104);
      v_5260 <- eval (extract v_5206 104 112);
      v_5261 <- eval (extract v_5208 104 112);
      v_5264 <- eval (extract v_5206 112 120);
      v_5265 <- eval (extract v_5208 112 120);
      v_5268 <- eval (extract v_5206 120 128);
      v_5269 <- eval (extract v_5208 120 128);
      setRegister (lhs.of_reg v_2693) (concat (mux (ult v_5207 v_5209) v_5207 v_5209) (concat (mux (ult v_5212 v_5213) v_5212 v_5213) (concat (mux (ult v_5216 v_5217) v_5216 v_5217) (concat (mux (ult v_5220 v_5221) v_5220 v_5221) (concat (mux (ult v_5224 v_5225) v_5224 v_5225) (concat (mux (ult v_5228 v_5229) v_5228 v_5229) (concat (mux (ult v_5232 v_5233) v_5232 v_5233) (concat (mux (ult v_5236 v_5237) v_5236 v_5237) (concat (mux (ult v_5240 v_5241) v_5240 v_5241) (concat (mux (ult v_5244 v_5245) v_5244 v_5245) (concat (mux (ult v_5248 v_5249) v_5248 v_5249) (concat (mux (ult v_5252 v_5253) v_5252 v_5253) (concat (mux (ult v_5256 v_5257) v_5256 v_5257) (concat (mux (ult v_5260 v_5261) v_5260 v_5261) (concat (mux (ult v_5264 v_5265) v_5264 v_5265) (mux (ult v_5268 v_5269) v_5268 v_5269))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2689 : Mem) (v_2688 : reg (bv 128)) => do
      v_12083 <- getRegister v_2688;
      v_12084 <- eval (extract v_12083 0 8);
      v_12085 <- evaluateAddress v_2689;
      v_12086 <- load v_12085 16;
      v_12087 <- eval (extract v_12086 0 8);
      v_12090 <- eval (extract v_12083 8 16);
      v_12091 <- eval (extract v_12086 8 16);
      v_12094 <- eval (extract v_12083 16 24);
      v_12095 <- eval (extract v_12086 16 24);
      v_12098 <- eval (extract v_12083 24 32);
      v_12099 <- eval (extract v_12086 24 32);
      v_12102 <- eval (extract v_12083 32 40);
      v_12103 <- eval (extract v_12086 32 40);
      v_12106 <- eval (extract v_12083 40 48);
      v_12107 <- eval (extract v_12086 40 48);
      v_12110 <- eval (extract v_12083 48 56);
      v_12111 <- eval (extract v_12086 48 56);
      v_12114 <- eval (extract v_12083 56 64);
      v_12115 <- eval (extract v_12086 56 64);
      v_12118 <- eval (extract v_12083 64 72);
      v_12119 <- eval (extract v_12086 64 72);
      v_12122 <- eval (extract v_12083 72 80);
      v_12123 <- eval (extract v_12086 72 80);
      v_12126 <- eval (extract v_12083 80 88);
      v_12127 <- eval (extract v_12086 80 88);
      v_12130 <- eval (extract v_12083 88 96);
      v_12131 <- eval (extract v_12086 88 96);
      v_12134 <- eval (extract v_12083 96 104);
      v_12135 <- eval (extract v_12086 96 104);
      v_12138 <- eval (extract v_12083 104 112);
      v_12139 <- eval (extract v_12086 104 112);
      v_12142 <- eval (extract v_12083 112 120);
      v_12143 <- eval (extract v_12086 112 120);
      v_12146 <- eval (extract v_12083 120 128);
      v_12147 <- eval (extract v_12086 120 128);
      setRegister (lhs.of_reg v_2688) (concat (mux (ult v_12084 v_12087) v_12084 v_12087) (concat (mux (ult v_12090 v_12091) v_12090 v_12091) (concat (mux (ult v_12094 v_12095) v_12094 v_12095) (concat (mux (ult v_12098 v_12099) v_12098 v_12099) (concat (mux (ult v_12102 v_12103) v_12102 v_12103) (concat (mux (ult v_12106 v_12107) v_12106 v_12107) (concat (mux (ult v_12110 v_12111) v_12110 v_12111) (concat (mux (ult v_12114 v_12115) v_12114 v_12115) (concat (mux (ult v_12118 v_12119) v_12118 v_12119) (concat (mux (ult v_12122 v_12123) v_12122 v_12123) (concat (mux (ult v_12126 v_12127) v_12126 v_12127) (concat (mux (ult v_12130 v_12131) v_12130 v_12131) (concat (mux (ult v_12134 v_12135) v_12134 v_12135) (concat (mux (ult v_12138 v_12139) v_12138 v_12139) (concat (mux (ult v_12142 v_12143) v_12142 v_12143) (mux (ult v_12146 v_12147) v_12146 v_12147))))))))))))))));
      pure ()
    pat_end
