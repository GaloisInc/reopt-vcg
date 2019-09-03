def pmaxsd1 : instruction :=
  definst "pmaxsd" $ do
    pattern fun (v_2557 : reg (bv 128)) (v_2558 : reg (bv 128)) => do
      v_4854 <- getRegister v_2558;
      v_4855 <- eval (extract v_4854 0 32);
      v_4856 <- getRegister v_2557;
      v_4857 <- eval (extract v_4856 0 32);
      v_4860 <- eval (extract v_4854 32 64);
      v_4861 <- eval (extract v_4856 32 64);
      v_4864 <- eval (extract v_4854 64 96);
      v_4865 <- eval (extract v_4856 64 96);
      v_4868 <- eval (extract v_4854 96 128);
      v_4869 <- eval (extract v_4856 96 128);
      setRegister (lhs.of_reg v_2558) (concat (mux (sgt v_4855 v_4857) v_4855 v_4857) (concat (mux (sgt v_4860 v_4861) v_4860 v_4861) (concat (mux (sgt v_4864 v_4865) v_4864 v_4865) (mux (sgt v_4868 v_4869) v_4868 v_4869))));
      pure ()
    pat_end;
    pattern fun (v_2552 : Mem) (v_2553 : reg (bv 128)) => do
      v_12254 <- getRegister v_2553;
      v_12255 <- eval (extract v_12254 0 32);
      v_12256 <- evaluateAddress v_2552;
      v_12257 <- load v_12256 16;
      v_12258 <- eval (extract v_12257 0 32);
      v_12261 <- eval (extract v_12254 32 64);
      v_12262 <- eval (extract v_12257 32 64);
      v_12265 <- eval (extract v_12254 64 96);
      v_12266 <- eval (extract v_12257 64 96);
      v_12269 <- eval (extract v_12254 96 128);
      v_12270 <- eval (extract v_12257 96 128);
      setRegister (lhs.of_reg v_2553) (concat (mux (sgt v_12255 v_12258) v_12255 v_12258) (concat (mux (sgt v_12261 v_12262) v_12261 v_12262) (concat (mux (sgt v_12265 v_12266) v_12265 v_12266) (mux (sgt v_12269 v_12270) v_12269 v_12270))));
      pure ()
    pat_end
