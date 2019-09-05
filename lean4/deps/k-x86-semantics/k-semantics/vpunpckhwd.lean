def vpunpckhwd1 : instruction :=
  definst "vpunpckhwd" $ do
    pattern fun (v_2710 : reg (bv 128)) (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_6243 <- getRegister v_2710;
      v_6245 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2712) (concat (concat (extract v_6243 0 16) (extract v_6245 0 16)) (concat (concat (extract v_6243 16 32) (extract v_6245 16 32)) (concat (concat (extract v_6243 32 48) (extract v_6245 32 48)) (concat (extract v_6243 48 64) (extract v_6245 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2721 : reg (bv 256)) (v_2722 : reg (bv 256)) (v_2723 : reg (bv 256)) => do
      v_6266 <- getRegister v_2721;
      v_6268 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2723) (concat (concat (extract v_6266 0 16) (extract v_6268 0 16)) (concat (concat (extract v_6266 16 32) (extract v_6268 16 32)) (concat (concat (extract v_6266 32 48) (extract v_6268 32 48)) (concat (concat (extract v_6266 48 64) (extract v_6268 48 64)) (concat (concat (extract v_6266 128 144) (extract v_6268 128 144)) (concat (concat (extract v_6266 144 160) (extract v_6268 144 160)) (concat (concat (extract v_6266 160 176) (extract v_6268 160 176)) (concat (extract v_6266 176 192) (extract v_6268 176 192)))))))));
      pure ()
    pat_end;
    pattern fun (v_2704 : Mem) (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) => do
      v_12309 <- evaluateAddress v_2704;
      v_12310 <- load v_12309 16;
      v_12312 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2706) (concat (concat (extract v_12310 0 16) (extract v_12312 0 16)) (concat (concat (extract v_12310 16 32) (extract v_12312 16 32)) (concat (concat (extract v_12310 32 48) (extract v_12312 32 48)) (concat (extract v_12310 48 64) (extract v_12312 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2716 : reg (bv 256)) (v_2717 : reg (bv 256)) => do
      v_12328 <- evaluateAddress v_2715;
      v_12329 <- load v_12328 32;
      v_12331 <- getRegister v_2716;
      setRegister (lhs.of_reg v_2717) (concat (concat (extract v_12329 0 16) (extract v_12331 0 16)) (concat (concat (extract v_12329 16 32) (extract v_12331 16 32)) (concat (concat (extract v_12329 32 48) (extract v_12331 32 48)) (concat (concat (extract v_12329 48 64) (extract v_12331 48 64)) (concat (concat (extract v_12329 128 144) (extract v_12331 128 144)) (concat (concat (extract v_12329 144 160) (extract v_12331 144 160)) (concat (concat (extract v_12329 160 176) (extract v_12331 160 176)) (concat (extract v_12329 176 192) (extract v_12331 176 192)))))))));
      pure ()
    pat_end
