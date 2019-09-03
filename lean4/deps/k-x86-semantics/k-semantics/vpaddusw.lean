def vpaddusw1 : instruction :=
  definst "vpaddusw" $ do
    pattern fun (v_2452 : reg (bv 128)) (v_2453 : reg (bv 128)) (v_2454 : reg (bv 128)) => do
      v_5457 <- getRegister v_2453;
      v_5460 <- getRegister v_2452;
      v_5463 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 0 16)) (concat (expression.bv_nat 1 0) (extract v_5460 0 16)));
      v_5472 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 16 32)) (concat (expression.bv_nat 1 0) (extract v_5460 16 32)));
      v_5481 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 32 48)) (concat (expression.bv_nat 1 0) (extract v_5460 32 48)));
      v_5490 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 48 64)) (concat (expression.bv_nat 1 0) (extract v_5460 48 64)));
      v_5499 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 64 80)) (concat (expression.bv_nat 1 0) (extract v_5460 64 80)));
      v_5508 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 80 96)) (concat (expression.bv_nat 1 0) (extract v_5460 80 96)));
      v_5517 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 96 112)) (concat (expression.bv_nat 1 0) (extract v_5460 96 112)));
      v_5526 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5457 112 128)) (concat (expression.bv_nat 1 0) (extract v_5460 112 128)));
      setRegister (lhs.of_reg v_2454) (concat (mux (eq (extract v_5463 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5463 1 17)) (concat (mux (eq (extract v_5472 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5472 1 17)) (concat (mux (eq (extract v_5481 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5481 1 17)) (concat (mux (eq (extract v_5490 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5490 1 17)) (concat (mux (eq (extract v_5499 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5499 1 17)) (concat (mux (eq (extract v_5508 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5508 1 17)) (concat (mux (eq (extract v_5517 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5517 1 17)) (mux (eq (extract v_5526 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5526 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2463 : reg (bv 256)) (v_2464 : reg (bv 256)) (v_2465 : reg (bv 256)) => do
      v_5544 <- getRegister v_2464;
      v_5547 <- getRegister v_2463;
      v_5550 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 0 16)) (concat (expression.bv_nat 1 0) (extract v_5547 0 16)));
      v_5559 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 16 32)) (concat (expression.bv_nat 1 0) (extract v_5547 16 32)));
      v_5568 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 32 48)) (concat (expression.bv_nat 1 0) (extract v_5547 32 48)));
      v_5577 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 48 64)) (concat (expression.bv_nat 1 0) (extract v_5547 48 64)));
      v_5586 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 64 80)) (concat (expression.bv_nat 1 0) (extract v_5547 64 80)));
      v_5595 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 80 96)) (concat (expression.bv_nat 1 0) (extract v_5547 80 96)));
      v_5604 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 96 112)) (concat (expression.bv_nat 1 0) (extract v_5547 96 112)));
      v_5613 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 112 128)) (concat (expression.bv_nat 1 0) (extract v_5547 112 128)));
      v_5622 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 128 144)) (concat (expression.bv_nat 1 0) (extract v_5547 128 144)));
      v_5631 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 144 160)) (concat (expression.bv_nat 1 0) (extract v_5547 144 160)));
      v_5640 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 160 176)) (concat (expression.bv_nat 1 0) (extract v_5547 160 176)));
      v_5649 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 176 192)) (concat (expression.bv_nat 1 0) (extract v_5547 176 192)));
      v_5658 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 192 208)) (concat (expression.bv_nat 1 0) (extract v_5547 192 208)));
      v_5667 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 208 224)) (concat (expression.bv_nat 1 0) (extract v_5547 208 224)));
      v_5676 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 224 240)) (concat (expression.bv_nat 1 0) (extract v_5547 224 240)));
      v_5685 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5544 240 256)) (concat (expression.bv_nat 1 0) (extract v_5547 240 256)));
      setRegister (lhs.of_reg v_2465) (concat (mux (eq (extract v_5550 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5550 1 17)) (concat (mux (eq (extract v_5559 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5559 1 17)) (concat (mux (eq (extract v_5568 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5568 1 17)) (concat (mux (eq (extract v_5577 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5577 1 17)) (concat (mux (eq (extract v_5586 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5586 1 17)) (concat (mux (eq (extract v_5595 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5595 1 17)) (concat (mux (eq (extract v_5604 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5604 1 17)) (concat (mux (eq (extract v_5613 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5613 1 17)) (concat (mux (eq (extract v_5622 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5622 1 17)) (concat (mux (eq (extract v_5631 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5631 1 17)) (concat (mux (eq (extract v_5640 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5640 1 17)) (concat (mux (eq (extract v_5649 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5649 1 17)) (concat (mux (eq (extract v_5658 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5658 1 17)) (concat (mux (eq (extract v_5667 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5667 1 17)) (concat (mux (eq (extract v_5676 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5676 1 17)) (mux (eq (extract v_5685 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5685 1 17)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2446 : Mem) (v_2447 : reg (bv 128)) (v_2448 : reg (bv 128)) => do
      v_14813 <- getRegister v_2447;
      v_14816 <- evaluateAddress v_2446;
      v_14817 <- load v_14816 16;
      v_14820 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 0 16)) (concat (expression.bv_nat 1 0) (extract v_14817 0 16)));
      v_14829 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 16 32)) (concat (expression.bv_nat 1 0) (extract v_14817 16 32)));
      v_14838 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 32 48)) (concat (expression.bv_nat 1 0) (extract v_14817 32 48)));
      v_14847 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 48 64)) (concat (expression.bv_nat 1 0) (extract v_14817 48 64)));
      v_14856 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 64 80)) (concat (expression.bv_nat 1 0) (extract v_14817 64 80)));
      v_14865 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 80 96)) (concat (expression.bv_nat 1 0) (extract v_14817 80 96)));
      v_14874 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 96 112)) (concat (expression.bv_nat 1 0) (extract v_14817 96 112)));
      v_14883 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14813 112 128)) (concat (expression.bv_nat 1 0) (extract v_14817 112 128)));
      setRegister (lhs.of_reg v_2448) (concat (mux (eq (extract v_14820 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14820 1 17)) (concat (mux (eq (extract v_14829 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14829 1 17)) (concat (mux (eq (extract v_14838 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14838 1 17)) (concat (mux (eq (extract v_14847 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14847 1 17)) (concat (mux (eq (extract v_14856 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14856 1 17)) (concat (mux (eq (extract v_14865 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14865 1 17)) (concat (mux (eq (extract v_14874 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14874 1 17)) (mux (eq (extract v_14883 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14883 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2457 : Mem) (v_2458 : reg (bv 256)) (v_2459 : reg (bv 256)) => do
      v_14896 <- getRegister v_2458;
      v_14899 <- evaluateAddress v_2457;
      v_14900 <- load v_14899 32;
      v_14903 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 0 16)) (concat (expression.bv_nat 1 0) (extract v_14900 0 16)));
      v_14912 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 16 32)) (concat (expression.bv_nat 1 0) (extract v_14900 16 32)));
      v_14921 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 32 48)) (concat (expression.bv_nat 1 0) (extract v_14900 32 48)));
      v_14930 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 48 64)) (concat (expression.bv_nat 1 0) (extract v_14900 48 64)));
      v_14939 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 64 80)) (concat (expression.bv_nat 1 0) (extract v_14900 64 80)));
      v_14948 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 80 96)) (concat (expression.bv_nat 1 0) (extract v_14900 80 96)));
      v_14957 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 96 112)) (concat (expression.bv_nat 1 0) (extract v_14900 96 112)));
      v_14966 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 112 128)) (concat (expression.bv_nat 1 0) (extract v_14900 112 128)));
      v_14975 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 128 144)) (concat (expression.bv_nat 1 0) (extract v_14900 128 144)));
      v_14984 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 144 160)) (concat (expression.bv_nat 1 0) (extract v_14900 144 160)));
      v_14993 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 160 176)) (concat (expression.bv_nat 1 0) (extract v_14900 160 176)));
      v_15002 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 176 192)) (concat (expression.bv_nat 1 0) (extract v_14900 176 192)));
      v_15011 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 192 208)) (concat (expression.bv_nat 1 0) (extract v_14900 192 208)));
      v_15020 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 208 224)) (concat (expression.bv_nat 1 0) (extract v_14900 208 224)));
      v_15029 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 224 240)) (concat (expression.bv_nat 1 0) (extract v_14900 224 240)));
      v_15038 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14896 240 256)) (concat (expression.bv_nat 1 0) (extract v_14900 240 256)));
      setRegister (lhs.of_reg v_2459) (concat (mux (eq (extract v_14903 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14903 1 17)) (concat (mux (eq (extract v_14912 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14912 1 17)) (concat (mux (eq (extract v_14921 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14921 1 17)) (concat (mux (eq (extract v_14930 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14930 1 17)) (concat (mux (eq (extract v_14939 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14939 1 17)) (concat (mux (eq (extract v_14948 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14948 1 17)) (concat (mux (eq (extract v_14957 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14957 1 17)) (concat (mux (eq (extract v_14966 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14966 1 17)) (concat (mux (eq (extract v_14975 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14975 1 17)) (concat (mux (eq (extract v_14984 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14984 1 17)) (concat (mux (eq (extract v_14993 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14993 1 17)) (concat (mux (eq (extract v_15002 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_15002 1 17)) (concat (mux (eq (extract v_15011 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_15011 1 17)) (concat (mux (eq (extract v_15020 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_15020 1 17)) (concat (mux (eq (extract v_15029 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_15029 1 17)) (mux (eq (extract v_15038 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_15038 1 17)))))))))))))))));
      pure ()
    pat_end
