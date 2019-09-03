def pminub1 : instruction :=
  definst "pminub" $ do
    pattern fun (v_2643 : reg (bv 128)) (v_2644 : reg (bv 128)) => do
      v_5175 <- getRegister v_2644;
      v_5176 <- eval (extract v_5175 0 8);
      v_5177 <- getRegister v_2643;
      v_5178 <- eval (extract v_5177 0 8);
      v_5181 <- eval (extract v_5175 8 16);
      v_5182 <- eval (extract v_5177 8 16);
      v_5185 <- eval (extract v_5175 16 24);
      v_5186 <- eval (extract v_5177 16 24);
      v_5189 <- eval (extract v_5175 24 32);
      v_5190 <- eval (extract v_5177 24 32);
      v_5193 <- eval (extract v_5175 32 40);
      v_5194 <- eval (extract v_5177 32 40);
      v_5197 <- eval (extract v_5175 40 48);
      v_5198 <- eval (extract v_5177 40 48);
      v_5201 <- eval (extract v_5175 48 56);
      v_5202 <- eval (extract v_5177 48 56);
      v_5205 <- eval (extract v_5175 56 64);
      v_5206 <- eval (extract v_5177 56 64);
      v_5209 <- eval (extract v_5175 64 72);
      v_5210 <- eval (extract v_5177 64 72);
      v_5213 <- eval (extract v_5175 72 80);
      v_5214 <- eval (extract v_5177 72 80);
      v_5217 <- eval (extract v_5175 80 88);
      v_5218 <- eval (extract v_5177 80 88);
      v_5221 <- eval (extract v_5175 88 96);
      v_5222 <- eval (extract v_5177 88 96);
      v_5225 <- eval (extract v_5175 96 104);
      v_5226 <- eval (extract v_5177 96 104);
      v_5229 <- eval (extract v_5175 104 112);
      v_5230 <- eval (extract v_5177 104 112);
      v_5233 <- eval (extract v_5175 112 120);
      v_5234 <- eval (extract v_5177 112 120);
      v_5237 <- eval (extract v_5175 120 128);
      v_5238 <- eval (extract v_5177 120 128);
      setRegister (lhs.of_reg v_2644) (concat (mux (ult v_5176 v_5178) v_5176 v_5178) (concat (mux (ult v_5181 v_5182) v_5181 v_5182) (concat (mux (ult v_5185 v_5186) v_5185 v_5186) (concat (mux (ult v_5189 v_5190) v_5189 v_5190) (concat (mux (ult v_5193 v_5194) v_5193 v_5194) (concat (mux (ult v_5197 v_5198) v_5197 v_5198) (concat (mux (ult v_5201 v_5202) v_5201 v_5202) (concat (mux (ult v_5205 v_5206) v_5205 v_5206) (concat (mux (ult v_5209 v_5210) v_5209 v_5210) (concat (mux (ult v_5213 v_5214) v_5213 v_5214) (concat (mux (ult v_5217 v_5218) v_5217 v_5218) (concat (mux (ult v_5221 v_5222) v_5221 v_5222) (concat (mux (ult v_5225 v_5226) v_5225 v_5226) (concat (mux (ult v_5229 v_5230) v_5229 v_5230) (concat (mux (ult v_5233 v_5234) v_5233 v_5234) (mux (ult v_5237 v_5238) v_5237 v_5238))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2639 : Mem) (v_2640 : reg (bv 128)) => do
      v_12225 <- getRegister v_2640;
      v_12226 <- eval (extract v_12225 0 8);
      v_12227 <- evaluateAddress v_2639;
      v_12228 <- load v_12227 16;
      v_12229 <- eval (extract v_12228 0 8);
      v_12232 <- eval (extract v_12225 8 16);
      v_12233 <- eval (extract v_12228 8 16);
      v_12236 <- eval (extract v_12225 16 24);
      v_12237 <- eval (extract v_12228 16 24);
      v_12240 <- eval (extract v_12225 24 32);
      v_12241 <- eval (extract v_12228 24 32);
      v_12244 <- eval (extract v_12225 32 40);
      v_12245 <- eval (extract v_12228 32 40);
      v_12248 <- eval (extract v_12225 40 48);
      v_12249 <- eval (extract v_12228 40 48);
      v_12252 <- eval (extract v_12225 48 56);
      v_12253 <- eval (extract v_12228 48 56);
      v_12256 <- eval (extract v_12225 56 64);
      v_12257 <- eval (extract v_12228 56 64);
      v_12260 <- eval (extract v_12225 64 72);
      v_12261 <- eval (extract v_12228 64 72);
      v_12264 <- eval (extract v_12225 72 80);
      v_12265 <- eval (extract v_12228 72 80);
      v_12268 <- eval (extract v_12225 80 88);
      v_12269 <- eval (extract v_12228 80 88);
      v_12272 <- eval (extract v_12225 88 96);
      v_12273 <- eval (extract v_12228 88 96);
      v_12276 <- eval (extract v_12225 96 104);
      v_12277 <- eval (extract v_12228 96 104);
      v_12280 <- eval (extract v_12225 104 112);
      v_12281 <- eval (extract v_12228 104 112);
      v_12284 <- eval (extract v_12225 112 120);
      v_12285 <- eval (extract v_12228 112 120);
      v_12288 <- eval (extract v_12225 120 128);
      v_12289 <- eval (extract v_12228 120 128);
      setRegister (lhs.of_reg v_2640) (concat (mux (ult v_12226 v_12229) v_12226 v_12229) (concat (mux (ult v_12232 v_12233) v_12232 v_12233) (concat (mux (ult v_12236 v_12237) v_12236 v_12237) (concat (mux (ult v_12240 v_12241) v_12240 v_12241) (concat (mux (ult v_12244 v_12245) v_12244 v_12245) (concat (mux (ult v_12248 v_12249) v_12248 v_12249) (concat (mux (ult v_12252 v_12253) v_12252 v_12253) (concat (mux (ult v_12256 v_12257) v_12256 v_12257) (concat (mux (ult v_12260 v_12261) v_12260 v_12261) (concat (mux (ult v_12264 v_12265) v_12264 v_12265) (concat (mux (ult v_12268 v_12269) v_12268 v_12269) (concat (mux (ult v_12272 v_12273) v_12272 v_12273) (concat (mux (ult v_12276 v_12277) v_12276 v_12277) (concat (mux (ult v_12280 v_12281) v_12280 v_12281) (concat (mux (ult v_12284 v_12285) v_12284 v_12285) (mux (ult v_12288 v_12289) v_12288 v_12289))))))))))))))));
      pure ()
    pat_end
