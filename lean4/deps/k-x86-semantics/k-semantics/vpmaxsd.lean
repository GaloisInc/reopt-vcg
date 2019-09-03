def vpmaxsd1 : instruction :=
  definst "vpmaxsd" $ do
    pattern fun (v_3449 : reg (bv 128)) (v_3450 : reg (bv 128)) (v_3451 : reg (bv 128)) => do
      v_11169 <- getRegister v_3450;
      v_11170 <- eval (extract v_11169 0 32);
      v_11171 <- getRegister v_3449;
      v_11172 <- eval (extract v_11171 0 32);
      v_11175 <- eval (extract v_11169 32 64);
      v_11176 <- eval (extract v_11171 32 64);
      v_11179 <- eval (extract v_11169 64 96);
      v_11180 <- eval (extract v_11171 64 96);
      v_11183 <- eval (extract v_11169 96 128);
      v_11184 <- eval (extract v_11171 96 128);
      setRegister (lhs.of_reg v_3451) (concat (mux (sgt v_11170 v_11172) v_11170 v_11172) (concat (mux (sgt v_11175 v_11176) v_11175 v_11176) (concat (mux (sgt v_11179 v_11180) v_11179 v_11180) (mux (sgt v_11183 v_11184) v_11183 v_11184))));
      pure ()
    pat_end;
    pattern fun (v_3460 : reg (bv 256)) (v_3461 : reg (bv 256)) (v_3462 : reg (bv 256)) => do
      v_11196 <- getRegister v_3461;
      v_11197 <- eval (extract v_11196 0 32);
      v_11198 <- getRegister v_3460;
      v_11199 <- eval (extract v_11198 0 32);
      v_11202 <- eval (extract v_11196 32 64);
      v_11203 <- eval (extract v_11198 32 64);
      v_11206 <- eval (extract v_11196 64 96);
      v_11207 <- eval (extract v_11198 64 96);
      v_11210 <- eval (extract v_11196 96 128);
      v_11211 <- eval (extract v_11198 96 128);
      v_11214 <- eval (extract v_11196 128 160);
      v_11215 <- eval (extract v_11198 128 160);
      v_11218 <- eval (extract v_11196 160 192);
      v_11219 <- eval (extract v_11198 160 192);
      v_11222 <- eval (extract v_11196 192 224);
      v_11223 <- eval (extract v_11198 192 224);
      v_11226 <- eval (extract v_11196 224 256);
      v_11227 <- eval (extract v_11198 224 256);
      setRegister (lhs.of_reg v_3462) (concat (mux (sgt v_11197 v_11199) v_11197 v_11199) (concat (mux (sgt v_11202 v_11203) v_11202 v_11203) (concat (mux (sgt v_11206 v_11207) v_11206 v_11207) (concat (mux (sgt v_11210 v_11211) v_11210 v_11211) (concat (mux (sgt v_11214 v_11215) v_11214 v_11215) (concat (mux (sgt v_11218 v_11219) v_11218 v_11219) (concat (mux (sgt v_11222 v_11223) v_11222 v_11223) (mux (sgt v_11226 v_11227) v_11226 v_11227))))))));
      pure ()
    pat_end;
    pattern fun (v_3443 : Mem) (v_3444 : reg (bv 128)) (v_3445 : reg (bv 128)) => do
      v_20168 <- getRegister v_3444;
      v_20169 <- eval (extract v_20168 0 32);
      v_20170 <- evaluateAddress v_3443;
      v_20171 <- load v_20170 16;
      v_20172 <- eval (extract v_20171 0 32);
      v_20175 <- eval (extract v_20168 32 64);
      v_20176 <- eval (extract v_20171 32 64);
      v_20179 <- eval (extract v_20168 64 96);
      v_20180 <- eval (extract v_20171 64 96);
      v_20183 <- eval (extract v_20168 96 128);
      v_20184 <- eval (extract v_20171 96 128);
      setRegister (lhs.of_reg v_3445) (concat (mux (sgt v_20169 v_20172) v_20169 v_20172) (concat (mux (sgt v_20175 v_20176) v_20175 v_20176) (concat (mux (sgt v_20179 v_20180) v_20179 v_20180) (mux (sgt v_20183 v_20184) v_20183 v_20184))));
      pure ()
    pat_end;
    pattern fun (v_3454 : Mem) (v_3455 : reg (bv 256)) (v_3456 : reg (bv 256)) => do
      v_20191 <- getRegister v_3455;
      v_20192 <- eval (extract v_20191 0 32);
      v_20193 <- evaluateAddress v_3454;
      v_20194 <- load v_20193 32;
      v_20195 <- eval (extract v_20194 0 32);
      v_20198 <- eval (extract v_20191 32 64);
      v_20199 <- eval (extract v_20194 32 64);
      v_20202 <- eval (extract v_20191 64 96);
      v_20203 <- eval (extract v_20194 64 96);
      v_20206 <- eval (extract v_20191 96 128);
      v_20207 <- eval (extract v_20194 96 128);
      v_20210 <- eval (extract v_20191 128 160);
      v_20211 <- eval (extract v_20194 128 160);
      v_20214 <- eval (extract v_20191 160 192);
      v_20215 <- eval (extract v_20194 160 192);
      v_20218 <- eval (extract v_20191 192 224);
      v_20219 <- eval (extract v_20194 192 224);
      v_20222 <- eval (extract v_20191 224 256);
      v_20223 <- eval (extract v_20194 224 256);
      setRegister (lhs.of_reg v_3456) (concat (mux (sgt v_20192 v_20195) v_20192 v_20195) (concat (mux (sgt v_20198 v_20199) v_20198 v_20199) (concat (mux (sgt v_20202 v_20203) v_20202 v_20203) (concat (mux (sgt v_20206 v_20207) v_20206 v_20207) (concat (mux (sgt v_20210 v_20211) v_20210 v_20211) (concat (mux (sgt v_20214 v_20215) v_20214 v_20215) (concat (mux (sgt v_20218 v_20219) v_20218 v_20219) (mux (sgt v_20222 v_20223) v_20222 v_20223))))))));
      pure ()
    pat_end
