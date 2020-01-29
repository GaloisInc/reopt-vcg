def vsqrtps : instruction :=
  definst "vsqrtps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ sqrt_single v_4) (concat (/- (_) -/ sqrt_single v_5) (concat (/- (_) -/ sqrt_single v_6) (/- (_) -/ sqrt_single v_7))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_9 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_10 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_11 : expression (bv 32)) <- eval (extract v_3 224 256);
      setRegister (lhs.of_reg ymm_1) (concat (/- (_) -/ sqrt_single v_4) (concat (/- (_) -/ sqrt_single v_5) (concat (/- (_) -/ sqrt_single v_6) (concat (/- (_) -/ sqrt_single v_7) (concat (/- (_) -/ sqrt_single v_8) (concat (/- (_) -/ sqrt_single v_9) (concat (/- (_) -/ sqrt_single v_10) (/- (_) -/ sqrt_single v_11))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ sqrt_single v_3) (concat (/- (_) -/ sqrt_single v_4) (concat (/- (_) -/ sqrt_single v_5) (/- (_) -/ sqrt_single v_6))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_7 : expression (bv 32)) <- eval (extract v_2 128 160);
      (v_8 : expression (bv 32)) <- eval (extract v_2 160 192);
      (v_9 : expression (bv 32)) <- eval (extract v_2 192 224);
      (v_10 : expression (bv 32)) <- eval (extract v_2 224 256);
      setRegister (lhs.of_reg ymm_1) (concat (/- (_) -/ sqrt_single v_3) (concat (/- (_) -/ sqrt_single v_4) (concat (/- (_) -/ sqrt_single v_5) (concat (/- (_) -/ sqrt_single v_6) (concat (/- (_) -/ sqrt_single v_7) (concat (/- (_) -/ sqrt_single v_8) (concat (/- (_) -/ sqrt_single v_9) (/- (_) -/ sqrt_single v_10))))))));
      pure ()
    pat_end
