def pminuw1 : instruction :=
  definst "pminuw" $ do
    pattern fun (v_2710 : reg (bv 128)) (v_2711 : reg (bv 128)) => do
      v_5318 <- getRegister v_2711;
      v_5319 <- eval (extract v_5318 0 16);
      v_5320 <- getRegister v_2710;
      v_5321 <- eval (extract v_5320 0 16);
      v_5324 <- eval (extract v_5318 16 32);
      v_5325 <- eval (extract v_5320 16 32);
      v_5328 <- eval (extract v_5318 32 48);
      v_5329 <- eval (extract v_5320 32 48);
      v_5332 <- eval (extract v_5318 48 64);
      v_5333 <- eval (extract v_5320 48 64);
      v_5336 <- eval (extract v_5318 64 80);
      v_5337 <- eval (extract v_5320 64 80);
      v_5340 <- eval (extract v_5318 80 96);
      v_5341 <- eval (extract v_5320 80 96);
      v_5344 <- eval (extract v_5318 96 112);
      v_5345 <- eval (extract v_5320 96 112);
      v_5348 <- eval (extract v_5318 112 128);
      v_5349 <- eval (extract v_5320 112 128);
      setRegister (lhs.of_reg v_2711) (concat (mux (ult v_5319 v_5321) v_5319 v_5321) (concat (mux (ult v_5324 v_5325) v_5324 v_5325) (concat (mux (ult v_5328 v_5329) v_5328 v_5329) (concat (mux (ult v_5332 v_5333) v_5332 v_5333) (concat (mux (ult v_5336 v_5337) v_5336 v_5337) (concat (mux (ult v_5340 v_5341) v_5340 v_5341) (concat (mux (ult v_5344 v_5345) v_5344 v_5345) (mux (ult v_5348 v_5349) v_5348 v_5349))))))));
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) (v_2706 : reg (bv 128)) => do
      v_12189 <- getRegister v_2706;
      v_12190 <- eval (extract v_12189 0 16);
      v_12191 <- evaluateAddress v_2707;
      v_12192 <- load v_12191 16;
      v_12193 <- eval (extract v_12192 0 16);
      v_12196 <- eval (extract v_12189 16 32);
      v_12197 <- eval (extract v_12192 16 32);
      v_12200 <- eval (extract v_12189 32 48);
      v_12201 <- eval (extract v_12192 32 48);
      v_12204 <- eval (extract v_12189 48 64);
      v_12205 <- eval (extract v_12192 48 64);
      v_12208 <- eval (extract v_12189 64 80);
      v_12209 <- eval (extract v_12192 64 80);
      v_12212 <- eval (extract v_12189 80 96);
      v_12213 <- eval (extract v_12192 80 96);
      v_12216 <- eval (extract v_12189 96 112);
      v_12217 <- eval (extract v_12192 96 112);
      v_12220 <- eval (extract v_12189 112 128);
      v_12221 <- eval (extract v_12192 112 128);
      setRegister (lhs.of_reg v_2706) (concat (mux (ult v_12190 v_12193) v_12190 v_12193) (concat (mux (ult v_12196 v_12197) v_12196 v_12197) (concat (mux (ult v_12200 v_12201) v_12200 v_12201) (concat (mux (ult v_12204 v_12205) v_12204 v_12205) (concat (mux (ult v_12208 v_12209) v_12208 v_12209) (concat (mux (ult v_12212 v_12213) v_12212 v_12213) (concat (mux (ult v_12216 v_12217) v_12216 v_12217) (mux (ult v_12220 v_12221) v_12220 v_12221))))))));
      pure ()
    pat_end
