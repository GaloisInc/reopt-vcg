def pminuw1 : instruction :=
  definst "pminuw" $ do
    pattern fun (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_5345 <- getRegister v_2739;
      v_5346 <- eval (extract v_5345 0 16);
      v_5347 <- getRegister v_2738;
      v_5348 <- eval (extract v_5347 0 16);
      v_5351 <- eval (extract v_5345 16 32);
      v_5352 <- eval (extract v_5347 16 32);
      v_5355 <- eval (extract v_5345 32 48);
      v_5356 <- eval (extract v_5347 32 48);
      v_5359 <- eval (extract v_5345 48 64);
      v_5360 <- eval (extract v_5347 48 64);
      v_5363 <- eval (extract v_5345 64 80);
      v_5364 <- eval (extract v_5347 64 80);
      v_5367 <- eval (extract v_5345 80 96);
      v_5368 <- eval (extract v_5347 80 96);
      v_5371 <- eval (extract v_5345 96 112);
      v_5372 <- eval (extract v_5347 96 112);
      v_5375 <- eval (extract v_5345 112 128);
      v_5376 <- eval (extract v_5347 112 128);
      setRegister (lhs.of_reg v_2739) (concat (mux (ult v_5346 v_5348) v_5346 v_5348) (concat (mux (ult v_5351 v_5352) v_5351 v_5352) (concat (mux (ult v_5355 v_5356) v_5355 v_5356) (concat (mux (ult v_5359 v_5360) v_5359 v_5360) (concat (mux (ult v_5363 v_5364) v_5363 v_5364) (concat (mux (ult v_5367 v_5368) v_5367 v_5368) (concat (mux (ult v_5371 v_5372) v_5371 v_5372) (mux (ult v_5375 v_5376) v_5375 v_5376))))))));
      pure ()
    pat_end;
    pattern fun (v_2734 : Mem) (v_2735 : reg (bv 128)) => do
      v_12165 <- getRegister v_2735;
      v_12166 <- eval (extract v_12165 0 16);
      v_12167 <- evaluateAddress v_2734;
      v_12168 <- load v_12167 16;
      v_12169 <- eval (extract v_12168 0 16);
      v_12172 <- eval (extract v_12165 16 32);
      v_12173 <- eval (extract v_12168 16 32);
      v_12176 <- eval (extract v_12165 32 48);
      v_12177 <- eval (extract v_12168 32 48);
      v_12180 <- eval (extract v_12165 48 64);
      v_12181 <- eval (extract v_12168 48 64);
      v_12184 <- eval (extract v_12165 64 80);
      v_12185 <- eval (extract v_12168 64 80);
      v_12188 <- eval (extract v_12165 80 96);
      v_12189 <- eval (extract v_12168 80 96);
      v_12192 <- eval (extract v_12165 96 112);
      v_12193 <- eval (extract v_12168 96 112);
      v_12196 <- eval (extract v_12165 112 128);
      v_12197 <- eval (extract v_12168 112 128);
      setRegister (lhs.of_reg v_2735) (concat (mux (ult v_12166 v_12169) v_12166 v_12169) (concat (mux (ult v_12172 v_12173) v_12172 v_12173) (concat (mux (ult v_12176 v_12177) v_12176 v_12177) (concat (mux (ult v_12180 v_12181) v_12180 v_12181) (concat (mux (ult v_12184 v_12185) v_12184 v_12185) (concat (mux (ult v_12188 v_12189) v_12188 v_12189) (concat (mux (ult v_12192 v_12193) v_12192 v_12193) (mux (ult v_12196 v_12197) v_12196 v_12197))))))));
      pure ()
    pat_end
