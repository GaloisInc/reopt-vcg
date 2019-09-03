def vpmaxud1 : instruction :=
  definst "vpmaxud" $ do
    pattern fun (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) (v_2421 : reg (bv 128)) => do
      v_4174 <- getRegister v_2420;
      v_4175 <- eval (extract v_4174 0 32);
      v_4176 <- getRegister v_2419;
      v_4177 <- eval (extract v_4176 0 32);
      v_4180 <- eval (extract v_4174 32 64);
      v_4181 <- eval (extract v_4176 32 64);
      v_4184 <- eval (extract v_4174 64 96);
      v_4185 <- eval (extract v_4176 64 96);
      v_4188 <- eval (extract v_4174 96 128);
      v_4189 <- eval (extract v_4176 96 128);
      setRegister (lhs.of_reg v_2421) (concat (mux (ugt v_4175 v_4177) v_4175 v_4177) (concat (mux (ugt v_4180 v_4181) v_4180 v_4181) (concat (mux (ugt v_4184 v_4185) v_4184 v_4185) (mux (ugt v_4188 v_4189) v_4188 v_4189))));
      pure ()
    pat_end;
    pattern fun (v_2431 : reg (bv 256)) (v_2432 : reg (bv 256)) (v_2433 : reg (bv 256)) => do
      v_4201 <- getRegister v_2432;
      v_4202 <- eval (extract v_4201 0 32);
      v_4203 <- getRegister v_2431;
      v_4204 <- eval (extract v_4203 0 32);
      v_4207 <- eval (extract v_4201 32 64);
      v_4208 <- eval (extract v_4203 32 64);
      v_4211 <- eval (extract v_4201 64 96);
      v_4212 <- eval (extract v_4203 64 96);
      v_4215 <- eval (extract v_4201 96 128);
      v_4216 <- eval (extract v_4203 96 128);
      v_4219 <- eval (extract v_4201 128 160);
      v_4220 <- eval (extract v_4203 128 160);
      v_4223 <- eval (extract v_4201 160 192);
      v_4224 <- eval (extract v_4203 160 192);
      v_4227 <- eval (extract v_4201 192 224);
      v_4228 <- eval (extract v_4203 192 224);
      v_4231 <- eval (extract v_4201 224 256);
      v_4232 <- eval (extract v_4203 224 256);
      setRegister (lhs.of_reg v_2433) (concat (mux (ugt v_4202 v_4204) v_4202 v_4204) (concat (mux (ugt v_4207 v_4208) v_4207 v_4208) (concat (mux (ugt v_4211 v_4212) v_4211 v_4212) (concat (mux (ugt v_4215 v_4216) v_4215 v_4216) (concat (mux (ugt v_4219 v_4220) v_4219 v_4220) (concat (mux (ugt v_4223 v_4224) v_4223 v_4224) (concat (mux (ugt v_4227 v_4228) v_4227 v_4228) (mux (ugt v_4231 v_4232) v_4231 v_4232))))))));
      pure ()
    pat_end;
    pattern fun (v_2413 : Mem) (v_2414 : reg (bv 128)) (v_2415 : reg (bv 128)) => do
      v_11119 <- getRegister v_2414;
      v_11120 <- eval (extract v_11119 0 32);
      v_11121 <- evaluateAddress v_2413;
      v_11122 <- load v_11121 16;
      v_11123 <- eval (extract v_11122 0 32);
      v_11126 <- eval (extract v_11119 32 64);
      v_11127 <- eval (extract v_11122 32 64);
      v_11130 <- eval (extract v_11119 64 96);
      v_11131 <- eval (extract v_11122 64 96);
      v_11134 <- eval (extract v_11119 96 128);
      v_11135 <- eval (extract v_11122 96 128);
      setRegister (lhs.of_reg v_2415) (concat (mux (ugt v_11120 v_11123) v_11120 v_11123) (concat (mux (ugt v_11126 v_11127) v_11126 v_11127) (concat (mux (ugt v_11130 v_11131) v_11130 v_11131) (mux (ugt v_11134 v_11135) v_11134 v_11135))));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2426 : reg (bv 256)) (v_2427 : reg (bv 256)) => do
      v_11142 <- getRegister v_2426;
      v_11143 <- eval (extract v_11142 0 32);
      v_11144 <- evaluateAddress v_2424;
      v_11145 <- load v_11144 32;
      v_11146 <- eval (extract v_11145 0 32);
      v_11149 <- eval (extract v_11142 32 64);
      v_11150 <- eval (extract v_11145 32 64);
      v_11153 <- eval (extract v_11142 64 96);
      v_11154 <- eval (extract v_11145 64 96);
      v_11157 <- eval (extract v_11142 96 128);
      v_11158 <- eval (extract v_11145 96 128);
      v_11161 <- eval (extract v_11142 128 160);
      v_11162 <- eval (extract v_11145 128 160);
      v_11165 <- eval (extract v_11142 160 192);
      v_11166 <- eval (extract v_11145 160 192);
      v_11169 <- eval (extract v_11142 192 224);
      v_11170 <- eval (extract v_11145 192 224);
      v_11173 <- eval (extract v_11142 224 256);
      v_11174 <- eval (extract v_11145 224 256);
      setRegister (lhs.of_reg v_2427) (concat (mux (ugt v_11143 v_11146) v_11143 v_11146) (concat (mux (ugt v_11149 v_11150) v_11149 v_11150) (concat (mux (ugt v_11153 v_11154) v_11153 v_11154) (concat (mux (ugt v_11157 v_11158) v_11157 v_11158) (concat (mux (ugt v_11161 v_11162) v_11161 v_11162) (concat (mux (ugt v_11165 v_11166) v_11165 v_11166) (concat (mux (ugt v_11169 v_11170) v_11169 v_11170) (mux (ugt v_11173 v_11174) v_11173 v_11174))))))));
      pure ()
    pat_end
