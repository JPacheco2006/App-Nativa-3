import os, sys, sqlite3, csv, time, json, threading, queue, secrets, socket, urllib.parse, shutil, math, html, webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from datetime import datetime
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import cv2
from PIL import Image, ImageTk, ImageOps
import qrcode

ROOT=Path(__file__).resolve().parent
DATA=ROOT/'datos'; LABELS=ROOT/'etiquetas'; CAPTURES=ROOT/'capturas'; PRODUCT_IMAGES=ROOT/'imagenes_productos'; IA_IMAGES=ROOT/'fotos_ia'; FACTURAS=ROOT/'facturas'
for p in (DATA,LABELS,CAPTURES,PRODUCT_IMAGES,IA_IMAGES,FACTURAS):p.mkdir(exist_ok=True)
DB=DATA/'productos.db'
REMOTE_PORT=8765
REMOTE_TOKEN=secrets.token_urlsafe(18)
REMOTE_STATE={'camera':'detenida','last_product':None,'fps':0.0,'brightness':0.0,'reads':0,'alert':'','updated':''}
REMOTE_LOCK=threading.Lock()
COMMANDS=queue.Queue()

def update_remote(**kwargs):
    with REMOTE_LOCK:REMOTE_STATE.update(kwargs,updated=datetime.now().isoformat(timespec='seconds'))

class RemoteHandler(BaseHTTPRequestHandler):
    def log_message(self,*args):pass
    def _send(self,body,ctype='application/json',status=200):
        if isinstance(body,(dict,list)):body=json.dumps(body,ensure_ascii=False).encode('utf-8')
        elif isinstance(body,str):body=body.encode('utf-8')
        self.send_response(status);self.send_header('Content-Type',ctype+'; charset=utf-8')
        self.send_header('Cache-Control','no-store');self.send_header('X-Content-Type-Options','nosniff')
        self.send_header('Content-Security-Policy',"default-src 'self' 'unsafe-inline'")
        self.end_headers();self.wfile.write(body)
    def _authorized(self):
        token=self.headers.get('X-VisionAI-Token','')
        # Token via URL only for browser dashboard; commands require header token.
        return secrets.compare_digest(token,REMOTE_TOKEN)
    def do_GET(self):
        path=urllib.parse.urlsplit(self.path).path
        if path=='/':
            html='''<!doctype html><html lang="es"><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>VisionAI remoto</title><style>body{font:16px Arial;max-width:780px;margin:30px auto;padding:12px;background:#eef3f8;color:#17324d}main{background:white;padding:24px;border-radius:14px}button{padding:12px;background:#165e8c;color:white;border:0;border-radius:8px;margin:6px}pre{white-space:pre-wrap;background:#f1f5f9;padding:14px;border-radius:8px}</style><main><h1>VisionAI · Panel remoto</h1><p>Estado en tiempo real de la cámara, lecturas y sensores.</p><p>Clave de acceso: <input id="token" type="password" placeholder="Pegá la clave de la app"></p><button onclick="load()">Actualizar</button><button onclick="send('start')">Iniciar cámara</button><button onclick="send('stop')">Detener cámara</button><button onclick="send('photo')">Capturar foto</button><pre id="out">Introducí la clave y pulsá Actualizar.</pre></main><script>async function load(){let r=await fetch('/api/estado',{headers:{'X-VisionAI-Token':document.querySelector('#token').value}});document.querySelector('#out').textContent=JSON.stringify(await r.json(),null,2)}async function send(a){let r=await fetch('/api/control',{method:'POST',headers:{'Content-Type':'application/json','X-VisionAI-Token':document.querySelector('#token').value},body:JSON.stringify({action:a})});document.querySelector('#out').textContent=JSON.stringify(await r.json(),null,2);setTimeout(load,400)}setInterval(()=>{if(document.querySelector('#token').value)load()},2500)</script></html>'''
            return self._send(html,'text/html')
        if not self._authorized():return self._send({'error':'Clave de acceso incorrecta'},status=401)
        if path=='/api/estado':
            with REMOTE_LOCK:state=dict(REMOTE_STATE)
            return self._send(state)
        if path=='/api/productos':
            with connect() as con:rows=con.execute('SELECT codigo,nombre,precio,descripcion,existencias FROM productos ORDER BY codigo').fetchall()
            return self._send([dict(zip(('codigo','nombre','precio','descripcion','existencias'),r)) for r in rows])
        return self._send({'error':'No existe'},status=404)
    def do_POST(self):
        if not self._authorized():return self._send({'error':'Clave de acceso incorrecta'},status=401)
        if urllib.parse.urlsplit(self.path).path!='/api/control':return self._send({'error':'No existe'},status=404)
        try:
            n=int(self.headers.get('Content-Length','0'))
            if n<1 or n>1024:raise ValueError('Solicitud demasiado grande')
            action=json.loads(self.rfile.read(n)).get('action')
            if action not in ('start','stop','photo'):raise ValueError('Acción inválida')
            COMMANDS.put(action)
            return self._send({'ok':True,'mensaje':'Orden recibida','action':action})
        except (ValueError,TypeError,json.JSONDecodeError) as ex:return self._send({'error':str(ex)},status=400)

def launch_remote():
    server=ThreadingHTTPServer(('0.0.0.0',REMOTE_PORT),RemoteHandler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    return server


def connect():
    c=sqlite3.connect(DB)
    c.execute('CREATE TABLE IF NOT EXISTS productos (codigo TEXT PRIMARY KEY, nombre TEXT NOT NULL, precio REAL NOT NULL, descripcion TEXT NOT NULL, existencias INTEGER NOT NULL DEFAULT 0)')
    cols={r[1] for r in c.execute('PRAGMA table_info(productos)')}
    if 'imagen' not in cols:c.execute("ALTER TABLE productos ADD COLUMN imagen TEXT NOT NULL DEFAULT ''")
    c.execute('CREATE TABLE IF NOT EXISTS fotos_ia (id INTEGER PRIMARY KEY, codigo TEXT NOT NULL, ruta TEXT NOT NULL)')
    c.execute('CREATE TABLE IF NOT EXISTS lecturas (id INTEGER PRIMARY KEY, fecha TEXT, codigo TEXT, nombre TEXT, precio REAL)')
    c.execute('CREATE TABLE IF NOT EXISTS ventas (id INTEGER PRIMARY KEY AUTOINCREMENT, fecha TEXT NOT NULL, total_centavos INTEGER NOT NULL)')
    c.execute('CREATE TABLE IF NOT EXISTS venta_detalles (venta_id INTEGER NOT NULL, codigo TEXT NOT NULL, nombre TEXT NOT NULL, precio_centavos INTEGER NOT NULL, cantidad INTEGER NOT NULL)')
    c.commit();return c

class App:
    def __init__(self,root):
        self.root=root;root.title('VisionAI Tienda | Lector de productos');root.geometry('1150x740');root.minsize(950,600)
        self.cap=None;self.camera_index=0;self.last_frame=None;self.detector=cv2.QRCodeDetector();self.last_read={};self.last_text=''
        self.sample_start=time.monotonic();self.sample_count=0;self.remote_server=None
        self.selected_image='';self.last_image_code=None;self.photo_ref=None
        self.cart={};self.scanned_qrs=set();self.last_detected_code=None;self.cart_window=None;self.cart_table=None;self.cart_total=None
        self.ia_model=None;self.ia_processor=None;self.ia_busy=False;self.ia_vectors={};self.ia_status=tk.StringVar(value='IA: sin cargar (descarga inicial requiere internet)')
        self.build();self.refresh();self.root.protocol('WM_DELETE_WINDOW',self.close)
        try:
            self.remote_server=launch_remote()
            self.remote_label.set(f'Panel remoto: http://{self.local_ip()}:{REMOTE_PORT} | Clave: {REMOTE_TOKEN}')
        except OSError as e:self.remote_label.set('Panel remoto no disponible: '+str(e))
        self.root.after(250,self.poll_commands)
    def build(self):
        self.root.configure(bg='#eaf0f7')
        top=ttk.Frame(self.root,padding=10);top.pack(fill='x')
        ttk.Label(top,text='VisionAI Tienda',font=('Segoe UI',20,'bold')).pack(side='left',padx=8)
        ttk.Label(top,text='Cámara + procesamiento de imagen + SQLite',font=('Segoe UI',10)).pack(side='left',padx=10)
        body=ttk.Frame(self.root,padding=10);body.pack(fill='both',expand=True)
        left=ttk.Frame(body);left.pack(side='left',fill='both',expand=True)
        right=ttk.Frame(body,width=390);right.pack(side='left',fill='y',padx=(15,0));right.pack_propagate(False)
        # Botones SIEMPRE visibles arriba de la vista de camara.
        controls=ttk.Frame(left);controls.pack(side='top',fill='x',pady=(0,10))
        self.start_button=ttk.Button(controls,text='INICIAR CAMARA',command=self.start)
        self.start_button.pack(side='left',padx=3)
        ttk.Button(controls,text='DETENER',command=self.stop).pack(side='left',padx=3)
        ttk.Button(controls,text='FOTO',command=self.capture).pack(side='left',padx=3)
        ttk.Button(controls,text='CAMBIAR CAMARA',command=self.switch_camera).pack(side='left',padx=3)
        ttk.Button(controls,text='CARRITO / FACTURA',command=self.show_cart).pack(side='left',padx=3)
        ttk.Button(controls,text='CATÁLOGO / ELEGIR PRODUCTO',command=self.show_catalog_picker).pack(side='left',padx=3)
        ttk.Button(controls,text='VER QR',command=self.show_qrs).pack(side='left',padx=3)
        self.video=tk.Label(left,bg='#111923',fg='white',text='Presiona INICIAR CAMARA (arriba)',font=('Segoe UI',16))
        self.video.pack(side='top',fill='both',expand=True)
        ia_bar=ttk.Frame(left);ia_bar.pack(fill='x',pady=4)
        ttk.Button(ia_bar,text='IA: RECONOCER OBJETO CENTRADO',command=self.ia_camera).pack(side='left',padx=3)
        ttk.Button(ia_bar,text='IA: AÑADIR FOTOS AL PRODUCTO',command=self.ia_add_photos).pack(side='left',padx=3)
        ttk.Label(left,textvariable=self.ia_status,wraplength=680,foreground='#176a4c').pack(anchor='w')
        self.cart_status=tk.StringVar(value='Carrito: 0 artículos | $0.00 MXN')
        ttk.Label(left,textvariable=self.cart_status,foreground='#08773d',font=('Segoe UI',11,'bold')).pack(anchor='w')
        self.status=tk.StringVar(value='Listo. No se requiere YOLO ni entrenamiento.')
        self.remote_label=tk.StringVar(value='Iniciando servidor remoto...')
        ttk.Label(left,textvariable=self.remote_label,wraplength=680,foreground='#125a86').pack(anchor='w')
        self.signal=tk.StringVar(value='Sensores: cámara detenida | FPS 0 | Luminosidad 0')
        ttk.Label(left,textvariable=self.signal).pack(anchor='w')
        ttk.Label(left,textvariable=self.status,wraplength=650).pack(anchor='w')
        info=ttk.LabelFrame(right,text='Producto detectado',padding=12);info.pack(fill='x',pady=(0,12))
        self.display_name=tk.StringVar(value='Esperando producto...')
        self.display_code=tk.StringVar(value='Código: —')
        self.display_price=tk.StringVar(value='$ — MXN')
        self.display_desc=tk.StringVar(value='Colocá el QR de un producto frente a la cámara.')
        ttk.Label(info,textvariable=self.display_name,font=('Segoe UI',17,'bold'),wraplength=340).pack(anchor='w')
        ttk.Label(info,textvariable=self.display_code).pack(anchor='w',pady=3)
        ttk.Label(info,textvariable=self.display_price,font=('Segoe UI',20,'bold'),foreground='#08773d').pack(anchor='w',pady=6)
        ttk.Label(info,textvariable=self.display_desc,wraplength=340).pack(anchor='w',pady=3)
        self.product_photo=tk.Label(info,text='Imagen del producto',bg='#e9edf2',height=8,anchor='center')
        self.product_photo.pack(fill='x',pady=5)
        entry=ttk.LabelFrame(right,text='Registrar o actualizar producto',padding=12);entry.pack(fill='x')
        self.fields={}
        for label,key in [('Código (opcional)','codigo'),('Nombre','nombre'),('Precio MXN','precio'),('Descripción','descripcion'),('Existencias','existencias')]:
            ttk.Label(entry,text=label).pack(anchor='w')
            var=tk.StringVar();self.fields[key]=var
            ttk.Entry(entry,textvariable=var).pack(fill='x',pady=(0,5))
        ttk.Button(entry,text='ELEGIR FOTO DEL PRODUCTO',command=self.choose_image).pack(fill='x',pady=3)
        self.image_label=ttk.Label(entry,text='Sin imagen seleccionada',wraplength=330)
        self.image_label.pack(anchor='w')
        buttons=ttk.Frame(entry);buttons.pack(fill='x',pady=5)
        ttk.Button(buttons,text='Guardar + crear QR',command=self.save_product).pack(side='left',padx=2)
        ttk.Button(buttons,text='Limpiar',command=self.clear).pack(side='left',padx=2)
        catalog=ttk.LabelFrame(right,text='Catálogo',padding=8);catalog.pack(fill='both',expand=True,pady=10)
        self.table=ttk.Treeview(catalog,columns=('codigo','nombre','precio'),show='headings',height=7)
        for col,width in [('codigo',95),('nombre',160),('precio',90)]:self.table.heading(col,text=col.capitalize());self.table.column(col,width=width)
        self.table.pack(fill='both',expand=True);self.table.bind('<<TreeviewSelect>>',self.pick)
        qrbar=ttk.Frame(catalog);qrbar.pack(fill='x',pady=5)
        ttk.Button(qrbar,text='VER QR DE PRODUCTOS',command=self.show_qrs).pack(side='left',padx=2)
        ttk.Button(qrbar,text='Abrir carpeta QR',command=self.open_qr_folder).pack(side='left',padx=2)
        ttk.Button(catalog,text='Exportar historial CSV',command=self.export).pack(anchor='e',pady=5)
    def refresh(self):
        for i in self.table.get_children():self.table.delete(i)
        with connect() as con:
            for code,name,price in con.execute('SELECT codigo,nombre,precio FROM productos ORDER BY codigo'):
                self.table.insert('', 'end',values=(code,name,f'{price:.2f}'))
    def clear(self):
        for v in self.fields.values():v.set('')
        self.selected_image='';self.image_label.configure(text='Sin imagen seleccionada')
    def pick(self,_):
        selection=self.table.selection()
        if not selection:return
        code=self.table.item(selection[0],'values')[0]
        with connect() as con:row=con.execute('SELECT codigo,nombre,precio,descripcion,existencias FROM productos WHERE codigo=?',(code,)).fetchone()
        if row:
            for k,v in zip(('codigo','nombre','precio','descripcion','existencias'),row):self.fields[k].set(str(v))
            with connect() as con:pic=con.execute('SELECT imagen FROM productos WHERE codigo=?',(code,)).fetchone()
            self.selected_image=pic[0] if pic else ''
            self.image_label.configure(text=Path(self.selected_image).name if self.selected_image else 'Sin imagen seleccionada')
            self.show_product_image(self.selected_image)
    def save_product(self):
        code=self.fields['codigo'].get().strip()
        name=self.fields['nombre'].get().strip()
        desc=self.fields['descripcion'].get().strip()
        if not name:messagebox.showwarning('Falta nombre','Escribí el nombre del producto.');return
        try:
            price=float(self.fields['precio'].get().replace(',','.'))
            stock=int(self.fields['existencias'].get() or '0')
            if price<0 or stock<0:raise ValueError
        except ValueError:messagebox.showwarning('Datos inválidos','Precio y existencias deben ser números no negativos.');return
        with connect() as con:
            if not code:
                rows=con.execute('SELECT codigo FROM productos').fetchall()
                ids=[int(r[0][4:]) for r in rows if r[0].startswith('PRD-') and r[0][4:].isdigit()]
                code=f'PRD-{max(ids,default=0)+1:04d}'
            old=con.execute('SELECT imagen FROM productos WHERE codigo=?',(code,)).fetchone()
            pic=old[0] if old else ''
            if self.selected_image and Path(self.selected_image).is_file():
                try:
                    with Image.open(self.selected_image) as im:
                        im=ImageOps.exif_transpose(im).convert('RGB')
                        im.thumbnail((900,900))
                        target=PRODUCT_IMAGES/(code+'.jpg')
                        im.save(target,format='JPEG',quality=88)
                        pic=str(target)
                except (OSError,ValueError) as ex:
                    messagebox.showerror('Imagen','No se pudo guardar la foto: '+str(ex));return
            con.execute('INSERT INTO productos(codigo,nombre,precio,descripcion,existencias,imagen) VALUES(?,?,?,?,?,?) ON CONFLICT(codigo) DO UPDATE SET nombre=excluded.nombre,precio=excluded.precio,descripcion=excluded.descripcion,existencias=excluded.existencias,imagen=excluded.imagen',(code,name,price,desc,stock,pic))
        # QR codifica solamente el identificador. El precio viene de SQLite.
        qr=qrcode.QRCode(box_size=12,border=4,error_correction=qrcode.constants.ERROR_CORRECT_M)
        qr.add_data('VISIONAI:'+code);qr.make(fit=True)
        qrpath=LABELS/(code+'.png');qr.make_image(fill_color='black',back_color='white').save(qrpath)
        self.fields['codigo'].set(code);self.refresh()
        self.status.set('Producto guardado. QR: '+str(qrpath))
        messagebox.showinfo('Producto guardado',f'Código: {code}\nQR: {qrpath}\nAbrí la imagen del QR en otro dispositivo o imprimila para escanearla.')
    def choose_image(self):
        path=filedialog.askopenfilename(title='Seleccionar foto del producto',filetypes=[('Imágenes','*.png *.jpg *.jpeg *.webp *.bmp')])
        if path:
            self.selected_image=path
            self.image_label.configure(text=Path(path).name)
            self.show_product_image(path)

    def show_product_image(self,path):
        if not path or not Path(path).is_file():
            self.photo_ref=None
            self.product_photo.configure(image='',text='Producto sin fotografía',height=8)
            return
        try:
            with Image.open(path) as im:
                im=ImageOps.exif_transpose(im).convert('RGB')
                im.thumbnail((300,135))
                self.photo_ref=ImageTk.PhotoImage(im.copy())
            self.product_photo.configure(image=self.photo_ref,text='',height=135)
        except (OSError,ValueError):
            self.product_photo.configure(image='',text='No se pudo abrir la fotografía')

    def open_qr_folder(self):
        try:
            if sys.platform=='win32':os.startfile(str(LABELS))
            elif sys.platform=='darwin':__import__('subprocess').Popen(['open',str(LABELS)])
            else:__import__('subprocess').Popen(['xdg-open',str(LABELS)])
        except OSError as ex:messagebox.showerror('Carpeta QR',str(ex))

    def show_catalog_picker(self):
        """Selector accesible, incluso si el catálogo inferior queda fuera de pantalla."""
        win=tk.Toplevel(self.root)
        win.title('Catálogo de productos | Seleccionar')
        win.geometry('720x470')
        win.transient(self.root)
        header=ttk.Frame(win,padding=12);header.pack(fill='x')
        ttk.Label(header,text='Seleccioná un producto para editarlo o añadir fotos de IA',
                  font=('Segoe UI',12,'bold')).pack(anchor='w')
        search=tk.StringVar()
        ttk.Label(header,text='Buscar por nombre o código:').pack(anchor='w',pady=(10,0))
        ttk.Entry(header,textvariable=search).pack(fill='x')
        area=ttk.Frame(win,padding=(12,0,12,8));area.pack(fill='both',expand=True)
        columns=('codigo','nombre','precio','existencias')
        tree=ttk.Treeview(area,columns=columns,show='headings',selectmode='browse')
        for col,width in [('codigo',105),('nombre',310),('precio',110),('existencias',105)]:
            tree.heading(col,text=col.capitalize());tree.column(col,width=width)
        tree.pack(side='left',fill='both',expand=True)
        scroll=ttk.Scrollbar(area,orient='vertical',command=tree.yview)
        scroll.pack(side='right',fill='y');tree.configure(yscrollcommand=scroll.set)
        with connect() as con:
            rows=con.execute('SELECT codigo,nombre,precio,existencias FROM productos ORDER BY nombre').fetchall()
        def fill(*_):
            for item in tree.get_children():tree.delete(item)
            term=search.get().strip().casefold()
            for code,name,price,stock in rows:
                if term and term not in str(code).casefold() and term not in str(name).casefold():continue
                tree.insert('','end',values=(code,name,f'{float(price):.2f}',stock))
        search.trace_add('write',fill);fill()
        def choose(add_photos=False):
            selected=tree.selection()
            if not selected:
                messagebox.showinfo('Catálogo','Seleccioná primero un producto.',parent=win);return
            code=tree.item(selected[0],'values')[0]
            # Sincronizar con el formulario principal y el catálogo inferior.
            self.refresh()
            for item in self.table.get_children():
                if self.table.item(item,'values')[0]==code:
                    self.table.selection_set(item);self.table.see(item)
                    self.pick(None)
                    break
            win.destroy()
            self.status.set('Producto seleccionado: '+code)
            if add_photos:self.ia_add_photos()
        footer=ttk.Frame(win,padding=12);footer.pack(fill='x')
        ttk.Button(footer,text='SELECCIONAR PRODUCTO',command=choose).pack(side='left',padx=4)
        ttk.Button(footer,text='SELECCIONAR Y AÑADIR FOTOS IA',command=lambda:choose(True)).pack(side='left',padx=4)
        ttk.Button(footer,text='CERRAR',command=win.destroy).pack(side='right',padx=4)
        tree.bind('<Double-1>',lambda _:choose())
        if tree.get_children():tree.selection_set(tree.get_children()[0])
        win.grab_set()

    def show_qrs(self):
        win=tk.Toplevel(self.root);win.title('Códigos QR de los productos');win.geometry('650x520')
        top=ttk.Frame(win,padding=8);top.pack(fill='x')
        ttk.Label(top,text='Elegí un producto para ver su QR',font=('Segoe UI',12,'bold')).pack(side='left')
        ttk.Button(top,text='Abrir carpeta QR',command=self.open_qr_folder).pack(side='right')
        body=ttk.Frame(win,padding=8);body.pack(fill='both',expand=True)
        items=tk.Listbox(body,width=40);items.pack(side='left',fill='y',padx=(0,10))
        preview=tk.Label(body,text='Seleccioná un producto',bg='white');preview.pack(side='left',fill='both',expand=True)
        with connect() as con:rows=con.execute('SELECT codigo,nombre FROM productos ORDER BY codigo').fetchall()
        for code,name in rows:items.insert('end',f'{code}  |  {name}')
        def select(_=None):
            sel=items.curselection()
            if not sel:return
            code=rows[sel[0]][0];path=LABELS/(code+'.png')
            if not path.is_file():
                qr=qrcode.make('VISIONAI:'+code);qr.save(path)
            try:
                with Image.open(path) as im:
                    im.thumbnail((320,320));win.qr_img=ImageTk.PhotoImage(im.copy())
                preview.configure(image=win.qr_img,text='')
            except OSError as ex:messagebox.showerror('QR',str(ex))
        items.bind('<<ListboxSelect>>',select)
        if rows:items.selection_set(0);select()

    def start(self):
        self.stop()
        backend=cv2.CAP_DSHOW if sys.platform=='win32' else cv2.CAP_ANY
        self.cap=cv2.VideoCapture(self.camera_index,backend)
        if not self.cap.isOpened():
            self.cap.release();self.cap=cv2.VideoCapture(self.camera_index)
        if not self.cap.isOpened():
            self.status.set('ERROR: no se pudo abrir cámara '+str(self.camera_index));self.cap.release();self.cap=None;return
        self.cap.set(cv2.CAP_PROP_FRAME_WIDTH,640);self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT,480)
        self.cap.set(cv2.CAP_PROP_FOURCC,cv2.VideoWriter_fourcc(*'MJPG'))
        self.status.set('Cámara activa. Mostrá una etiqueta QR de VisionAI.')
        update_remote(camera='activa')
        self.update()
    def stop(self):
        if self.cap is not None:self.cap.release();self.cap=None
        update_remote(camera='detenida')
    def switch_camera(self):
        self.camera_index=(self.camera_index+1)%4;self.start()
    def read(self,frame):
        # detectAndDecodeMulti puede no estar disponible en algunas versiones.
        results=[]
        try:
            ok,decoded,points,_=self.detector.detectAndDecodeMulti(frame)
            if ok and points is not None:
                for text,quad in zip(decoded,points):
                    if text:results.append((text,quad))
        except (cv2.error,AttributeError):pass
        if not results:
            try:
                text,quad,_=self.detector.detectAndDecode(frame)
                if text and quad is not None:results.append((text,quad.reshape(4,2)))
            except cv2.error:pass
        return results
    def update(self):
        if self.cap is None:return
        ok,frame=self.cap.read()
        if ok:
            for payload,quad in self.read(frame):
                if not payload.startswith('VISIONAI:'):continue
                code=payload[len('VISIONAI:'):]
                with connect() as con:
                    row=con.execute('SELECT nombre,precio,descripcion,imagen FROM productos WHERE codigo=?',(code,)).fetchone()
                pts=quad.astype('int32').reshape(-1,1,2)
                color=(0,220,30) if row else (0,130,255)
                cv2.polylines(frame,[pts],True,color,3)
                label=(row[0]+' $'+f'{row[1]:.2f}') if row else 'Código no registrado'
                cv2.putText(frame,label,(max(0,int(pts[0,0,0])),max(24,int(pts[0,0,1])-12)),cv2.FONT_HERSHEY_SIMPLEX,.65,color,2,cv2.LINE_AA)
                if row:
                    self.display_name.set(row[0]);self.display_code.set('Código: '+code)
                    self.display_price.set(f'${row[1]:,.2f} MXN');self.display_desc.set(row[2] or 'Sin descripción')
                    if code!=self.last_image_code:
                        self.last_image_code=code;self.show_product_image(row[3])
                    now=time.monotonic()
                    if now-self.last_read.get(code,0)>6:
                        self.last_read[code]=now
                        with connect() as con:con.execute('INSERT INTO lecturas(fecha,codigo,nombre,precio) VALUES(?,?,?,?)',(datetime.now().isoformat(timespec='seconds'),code,row[0],row[1]))
                    self.status.set('DETECTADO: '+code+' | '+row[0])
                    self.last_detected_code=code
                    if code not in self.scanned_qrs:
                        self.scanned_qrs.add(code)
                        self.add_cart(code,source='QR')
                    with REMOTE_LOCK:current_reads=REMOTE_STATE['reads']
                    update_remote(last_product={'codigo':code,'nombre':row[0],'precio':row[1],'descripcion':row[2]},reads=current_reads+1)
                    with connect() as con:
                        stock=con.execute('SELECT existencias FROM productos WHERE codigo=?',(code,)).fetchone()[0]
                    update_remote(alert=('ALERTA AUTOMÁTICA: inventario bajo ('+str(stock)+') para '+code) if stock<=3 else '')
                else:self.status.set('QR detectado, pero el código no existe en la base de datos: '+code)
            self.last_frame=frame.copy()
            self.sample_count+=1
            elapsed=time.monotonic()-self.sample_start
            if elapsed>=1:
                fps=round(self.sample_count/elapsed,1)
                brightness=round(float(cv2.cvtColor(frame,cv2.COLOR_BGR2GRAY).mean()),1)
                self.signal.set(f'Sensores: cámara activa | FPS {fps} | Luminosidad {brightness}/255')
                update_remote(fps=fps,brightness=brightness)
                self.sample_start=time.monotonic();self.sample_count=0
            rgb=cv2.cvtColor(frame,cv2.COLOR_BGR2RGB)
            img=Image.fromarray(rgb)
            maxw=max(320,self.video.winfo_width()-8);maxh=max(240,self.video.winfo_height()-8)
            img.thumbnail((maxw,maxh))
            self.tkimg=ImageTk.PhotoImage(img)
            self.video.configure(image=self.tkimg,text='')
        else:self.status.set('No se pudo leer un fotograma de la cámara.')
        if self.cap is not None:self.root.after(30,self.update)

    def ia_add_photos(self):
        code=self.fields['codigo'].get().strip()
        if not code:
            self.show_catalog_picker()
            return
        with connect() as con:
            if not con.execute('SELECT 1 FROM productos WHERE codigo=?',(code,)).fetchone():
                messagebox.showwarning('Fotos IA','Guardá primero el producto.');return
        paths=filedialog.askopenfilenames(title='Fotografías del producto '+code,filetypes=[('Imágenes','*.jpg *.jpeg *.png *.webp *.bmp')])
        if not paths:return
        saved=0
        with connect() as con:
            for path in paths:
                try:
                    with Image.open(path) as im:
                        im=ImageOps.exif_transpose(im).convert('RGB')
                        if min(im.size)<50:continue
                        im.thumbnail((900,900))
                        target=IA_IMAGES/(code+'_'+str(time.time_ns())+'.jpg')
                        im.save(target,quality=92)
                    con.execute('INSERT INTO fotos_ia(codigo,ruta) VALUES(?,?)',(code,str(target)))
                    saved+=1
                except (OSError,ValueError):pass
        self.ia_vectors.clear()  # invalidate cache
        self.ia_status.set(f'IA: {saved} fotos añadidas a {code}. Ahora podés reconocerlo.')

    def ia_camera(self):
        if self.last_frame is None:
            messagebox.showinfo('IA','Iniciá la cámara y colocá un solo objeto en el centro.');return
        if self.ia_busy:return
        # Zona central fija para que la comparación no incluya todo el fondo.
        frame=self.last_frame.copy()
        h,w=frame.shape[:2]
        x1,y1,x2,y2=int(w*.18),int(h*.14),int(w*.82),int(h*.86)
        crop=frame[y1:y2,x1:x2]
        self.ia_busy=True
        self.ia_status.set('IA: procesando... Primera vez descargará SigLIP2 (~centenas de MB).')
        threading.Thread(target=self._ia_worker,args=(crop,),daemon=True).start()

    def _ia_worker(self,crop):
        try:
            import torch
            from transformers import AutoModel, AutoProcessor
            from PIL import Image as PILImage
            model_id='google/siglip2-base-patch16-224'
            if self.ia_model is None:
                self.ia_processor=AutoProcessor.from_pretrained(model_id)
                self.ia_model=AutoModel.from_pretrained(model_id).eval()
            with connect() as con:
                rows=con.execute("""SELECT p.codigo,p.nombre,p.precio,p.descripcion,p.imagen,f.ruta
                    FROM productos p LEFT JOIN fotos_ia f ON f.codigo=p.codigo
                    ORDER BY p.codigo""").fetchall()
            # La foto principal del catálogo también cuenta como ejemplo.
            refs={}
            for code,name,price,desc,main_pic,extra in rows:
                refs.setdefault(code,{'name':name,'price':price,'desc':desc,'images':[]})
                for path in (main_pic,extra):
                    if path and path not in refs[code]['images'] and Path(path).is_file():
                        refs[code]['images'].append(path)
            if not any(r['images'] for r in refs.values()):
                raise RuntimeError('No hay fotos registradas. Seleccioná un producto y añadí fotos IA.')
            def embed(image):
                inputs=self.ia_processor(images=image,return_tensors='pt')
                with torch.inference_mode():
                    v=self.ia_model.get_image_features(**inputs)
                    if not isinstance(v,torch.Tensor):
                        v=v.pooler_output if hasattr(v,'pooler_output') else v[0]
                    v=torch.nn.functional.normalize(v.float(),dim=-1)
                return v[0].cpu().numpy()
            if not self.ia_vectors:
                for code,item in refs.items():
                    vectors=[]
                    for path in item['images']:
                        try:
                            with PILImage.open(path) as im:
                                vectors.append(embed(ImageOps.exif_transpose(im).convert('RGB')))
                        except (OSError,ValueError):pass
                    if vectors:self.ia_vectors[code]=vectors
            query=embed(PILImage.fromarray(cv2.cvtColor(crop,cv2.COLOR_BGR2RGB)))
            ranks=[]
            for code,vectors in self.ia_vectors.items():
                scores=sorted((float(query @ v) for v in vectors),reverse=True)
                # Top-2 evita que una sola foto accidental domine.
                score=sum(scores[:2])/min(len(scores),2)
                ranks.append((score,code))
            ranks.sort(reverse=True)
            if not ranks:raise RuntimeError('No se pudieron procesar las fotografías.')
            score,code=ranks[0]
            second=ranks[1][0] if len(ranks)>1 else -1
            # Umbrales conservadores; NO son probabilidades ni garantía de precisión.
            if score<0.72 or (len(ranks)>1 and score-second<0.045):
                result=('unknown',score,second)
            else:
                item=refs[code]
                result=('found',code,item['name'],item['price'],item['desc'],score)
            self.root.after(0,lambda r=result:self._ia_result(r))
        except Exception as ex:
            msg=str(ex)
            self.root.after(0,lambda m=msg:self._ia_error(m))

    def _ia_error(self,msg):
        self.ia_busy=False
        self.ia_status.set('IA ERROR: '+msg[:220])

    def _ia_result(self,result):
        self.ia_busy=False
        if result[0]=='unknown':
            self.ia_status.set(f'IA: producto no identificado con suficiente confianza (similitud {result[1]:.2f}).')
            return
        _,code,name,price,desc,score=result
        self.display_name.set(name)
        self.display_code.set('Código: '+code+' (reconocimiento visual IA)')
        self.display_price.set(f'${price:,.2f} MXN')
        self.display_desc.set(desc or 'Sin descripción')
        with connect() as con:
            row=con.execute('SELECT imagen FROM productos WHERE codigo=?',(code,)).fetchone()
            con.execute('INSERT INTO lecturas(fecha,codigo,nombre,precio) VALUES(?,?,?,?)',
                        (datetime.now().isoformat(timespec='seconds'),code,name,price))
        self.show_product_image(row[0] if row else '')
        self.ia_status.set(f'IA: {name} identificado (similitud {score:.2f}; NO es probabilidad).')
        self.last_detected_code=code
        self.add_cart(code,source='IA')

    def add_cart(self,code,source='manual'):
        # Consultar el catálogo actual: nunca confiar en el precio predicho por la IA.
        with connect() as con:
            row=con.execute('SELECT nombre,precio,existencias FROM productos WHERE codigo=?',(code,)).fetchone()
        if not row:return
        name,price,stock=row
        current=self.cart.get(code,{}).get('cantidad',0)
        if current>=stock:
            self.status.set(f'No se agregó {name}: inventario insuficiente ({stock}).')
            return
        self.cart[code]={'nombre':name,'precio_centavos':round(float(price)*100),'cantidad':current+1}
        self.refresh_cart()
        self.status.set(f'Agregado al carrito por {source}: {name} (${float(price):.2f}).')

    def refresh_cart(self):
        count=sum(v['cantidad'] for v in self.cart.values())
        total=sum(v['cantidad']*v['precio_centavos'] for v in self.cart.values())
        self.cart_status.set(f'Carrito: {count} artículos | ${total/100:,.2f} MXN')
        if self.cart_window is None or not self.cart_window.winfo_exists():return
        for item in self.cart_table.get_children():self.cart_table.delete(item)
        for code,item in self.cart.items():
            self.cart_table.insert('', 'end',iid=code,values=(code,item['nombre'],item['cantidad'],f"${item['precio_centavos']/100:,.2f}",f"${item['cantidad']*item['precio_centavos']/100:,.2f}"))
        self.cart_total.set(f'TOTAL: ${total/100:,.2f} MXN')

    def show_cart(self):
        if self.cart_window is not None and self.cart_window.winfo_exists():
            self.cart_window.lift();self.refresh_cart();return
        win=tk.Toplevel(self.root);win.title('VisionAI | Carrito y factura');win.geometry('820x500');win.minsize(690,400)
        self.cart_window=win
        ttk.Label(win,text='Carrito de compras',font=('Segoe UI',18,'bold')).pack(anchor='w',padx=14,pady=12)
        ttk.Label(win,text='Los QR se agregan una vez por compra; la IA agrega una unidad por reconocimiento.').pack(anchor='w',padx=14)
        table=ttk.Treeview(win,columns=('codigo','nombre','cantidad','precio','subtotal'),show='headings',height=12)
        self.cart_table=table
        for col,width in [('codigo',110),('nombre',245),('cantidad',90),('precio',120),('subtotal',120)]:
            table.heading(col,text=col.capitalize());table.column(col,width=width,anchor='center' if col!='nombre' else 'w')
        table.pack(fill='both',expand=True,padx=14,pady=10)
        actions=ttk.Frame(win);actions.pack(fill='x',padx=14,pady=5)
        ttk.Button(actions,text='+1 UNIDAD',command=lambda:self.change_qty(1)).pack(side='left',padx=3)
        ttk.Button(actions,text='-1 UNIDAD',command=lambda:self.change_qty(-1)).pack(side='left',padx=3)
        ttk.Button(actions,text='QUITAR PRODUCTO',command=self.remove_cart_item).pack(side='left',padx=3)
        ttk.Button(actions,text='AÑADIR PRODUCTO SELECCIONADO',command=self.add_catalog_selected).pack(side='left',padx=3)
        bottom=ttk.Frame(win);bottom.pack(fill='x',padx=14,pady=12)
        self.cart_total=tk.StringVar()
        ttk.Label(bottom,textvariable=self.cart_total,font=('Segoe UI',16,'bold'),foreground='#08773d').pack(side='left')
        ttk.Button(bottom,text='FINALIZAR COMPRA Y GENERAR FACTURA',command=self.checkout).pack(side='right')
        self.refresh_cart()

    def selected_cart_code(self):
        if self.cart_table is None:return None
        selection=self.cart_table.selection()
        return selection[0] if selection else None

    def change_qty(self,delta):
        code=self.selected_cart_code()
        if not code:return
        if delta>0:self.add_cart(code,source='carrito')
        else:
            self.cart[code]['cantidad']-=1
            if self.cart[code]['cantidad']<=0:del self.cart[code]
            self.refresh_cart()

    def remove_cart_item(self):
        code=self.selected_cart_code()
        if code:
            del self.cart[code];self.refresh_cart()

    def add_catalog_selected(self):
        selection=self.table.selection()
        if not selection:
            messagebox.showinfo('Catálogo','Seleccioná un producto en el catálogo de la ventana principal.');return
        self.add_cart(self.table.item(selection[0],'values')[0],source='catálogo')

    def checkout(self):
        if not self.cart:
            messagebox.showinfo('Carrito','El carrito está vacío.');return
        total=sum(item['precio_centavos']*item['cantidad'] for item in self.cart.values())
        if not messagebox.askyesno('Confirmar compra',f'¿Finalizar compra por ${total/100:,.2f} MXN?\nSe descontarán las existencias.'):
            return
        try:
            with connect() as con:
                con.execute('BEGIN IMMEDIATE')
                # Validar todas las existencias antes de descontar ninguna.
                for code,item in self.cart.items():
                    row=con.execute('SELECT existencias FROM productos WHERE codigo=?',(code,)).fetchone()
                    if not row or row[0]<item['cantidad']:
                        raise ValueError(f'Existencias insuficientes para {code}. Actualizá el carrito.')
                date=datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                cur=con.execute('INSERT INTO ventas(fecha,total_centavos) VALUES(?,?)',(date,total))
                sale_id=cur.lastrowid
                items=[(code,v['nombre'],v['precio_centavos'],v['cantidad']) for code,v in self.cart.items()]
                for code,name,price,qty in items:
                    con.execute('INSERT INTO venta_detalles(venta_id,codigo,nombre,precio_centavos,cantidad) VALUES(?,?,?,?,?)',(sale_id,code,name,price,qty))
                    con.execute('UPDATE productos SET existencias=existencias-? WHERE codigo=?',(qty,code))
            # La factura se guarda como HTML imprimible, sin librerías adicionales.
            rows=''.join('<tr><td>'+html.escape(code)+'</td><td>'+html.escape(name)+'</td><td>'+str(qty)+'</td><td>$'+f'{price/100:,.2f}'+'</td><td>$'+f'{price*qty/100:,.2f}'+'</td></tr>' for code,name,price,qty in items)
            document=f"""<!doctype html><html lang="es"><head><meta charset="utf-8"><title>Factura VisionAI #{sale_id:06d}</title><style>body{{font:15px Arial;max-width:820px;margin:45px auto;color:#1c2b3a}}h1{{color:#146a45}}table{{border-collapse:collapse;width:100%;margin:25px 0}}th,td{{padding:11px;border-bottom:1px solid #ddd;text-align:left}}th{{background:#edf3f5}}.total{{font-size:25px;text-align:right;font-weight:bold}}@media print{{button{{display:none}}}}</style></head><body><h1>VisionAI Tienda</h1><h2>Comprobante de compra #{sale_id:06d}</h2><p>Fecha: {date}<br>Moneda: MXN</p><table><thead><tr><th>Código</th><th>Producto</th><th>Cant.</th><th>Precio</th><th>Subtotal</th></tr></thead><tbody>{rows}</tbody></table><p class="total">TOTAL: ${total/100:,.2f} MXN</p><p>Comprobante de demostración académica. No es un CFDI ni una factura fiscal válida.</p><button onclick="window.print()">Imprimir / Guardar como PDF</button></body></html>"""
            path=FACTURAS/f'Factura_{sale_id:06d}.html'
            path.write_text(document,encoding='utf-8')
            self.cart.clear();self.scanned_qrs.clear();self.refresh_cart();self.refresh()
            self.status.set('Compra completada. Factura: '+str(path))
            webbrowser.open(path.resolve().as_uri())
            messagebox.showinfo('Compra completada',f'Factura #{sale_id:06d} creada.\nTotal: ${total/100:,.2f} MXN\nArchivo: {path}\nSe abrió en tu navegador para imprimir o guardar como PDF.')
        except (sqlite3.Error,ValueError,OSError) as ex:
            messagebox.showerror('Error al finalizar',str(ex))

    def capture(self):
        if self.last_frame is None:messagebox.showinfo('Cámara','Primero iniciá la cámara.');return
        path=CAPTURES/(datetime.now().strftime('%Y%m%d_%H%M%S')+'.jpg')
        cv2.imwrite(str(path),self.last_frame);self.status.set('Captura: '+str(path))
    def export(self):
        path=filedialog.asksaveasfilename(defaultextension='.csv',filetypes=[('CSV','*.csv')],initialfile='historial_visionai.csv')
        if not path:return
        with connect() as con:rows=con.execute('SELECT fecha,codigo,nombre,precio FROM lecturas ORDER BY id').fetchall()
        with open(path,'w',newline='',encoding='utf-8-sig') as f:
            writer=csv.writer(f);writer.writerow(['fecha','codigo','nombre','precio_MXN']);writer.writerows(rows)
        self.status.set('Historial exportado: '+path)
    @staticmethod
    def local_ip():
        try:
            s=socket.socket(socket.AF_INET,socket.SOCK_DGRAM)
            s.connect(('192.0.2.1',80));ip=s.getsockname()[0];s.close();return ip
        except OSError:return '127.0.0.1'
    def poll_commands(self):
        try:
            while True:
                action=COMMANDS.get_nowait()
                if action=='start':self.start()
                elif action=='stop':self.stop()
                elif action=='photo':self.capture()
        except queue.Empty:pass
        self.root.after(250,self.poll_commands)
    def close(self):
        self.stop()
        if self.remote_server:self.remote_server.shutdown();self.remote_server.server_close()
        self.root.destroy()

if __name__=='__main__':
    connect().close()
    root=tk.Tk()
    try:ttk.Style().theme_use('clam')
    except tk.TclError:pass
    App(root);root.mainloop()
