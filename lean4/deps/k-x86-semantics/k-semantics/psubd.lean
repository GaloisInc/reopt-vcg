def psubd1 : instruction :=
  definst "psubd" $ do
    pattern fun (v_3090 : reg (bv 128)) (v_3091 : reg (bv 128)) => do
      v_8351 <- getRegister v_3091;
      v_8353 <- getRegister v_3090;
      setRegister (lhs.of_reg v_3091) (concat (sub (extract v_8351 0 32) (extract v_8353 0 32)) (concat (sub (extract v_8351 32 64) (extract v_8353 32 64)) (concat (sub (extract v_8351 64 96) (extract v_8353 64 96)) (sub (extract v_8351 96 128) (extract v_8353 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3086 : reg (bv 128)) => do
      v_15265 <- getRegister v_3086;
      v_15267 <- evaluateAddress v_3085;
      v_15268 <- load v_15267 16;
      setRegister (lhs.of_reg v_3086) (concat (sub (extract v_15265 0 32) (extract v_15268 0 32)) (concat (sub (extract v_15265 32 64) (extract v_15268 32 64)) (concat (sub (extract v_15265 64 96) (extract v_15268 64 96)) (sub (extract v_15265 96 128) (extract v_15268 96 128)))));
      pure ()
    pat_end
